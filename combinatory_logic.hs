------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x : xs) (y : ys)
  | x == y = x : merge xs ys
  | x <= y = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x : xs) (y : ys)
  | x < y = x : minus xs (y : ys)
  | x == y = minus xs ys
  | otherwise = minus (x : xs) ys

variables :: [Var]
variables = [[x] | x <- ['a' .. 'z']] ++ [x : show i | i <- [1 ..], x <- ['a' .. 'z']]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [x | x <- xs, not (elem x ys)]

fresh :: [Var] -> Var
fresh = head . removeAll variables

-- - - - - - - - - - - -- Terms

type Var = String

data Term
  = Variable Var
  | Lambda Var Term
  | Apply Term Term

pretty :: Term -> String
pretty = f 0
  where
    f i (Variable x) = x
    f i (Lambda x m) = if elem i [2, 3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m
    f i (Apply m n) = if elem i [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0 = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i - 1))

-- - - - - - - - - - - -- Renaming, substitution, beta-reduction

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply m n) = used n `merge` used m

rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
  | y == x = Variable z
  | otherwise = Variable x
rename y z (Lambda x m)
  | y == x = Lambda x m
  | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)

substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
  | y == x = p
  | otherwise = Variable x
substitute y p (Lambda x m)
  | y == x = Lambda x m
  | otherwise = Lambda z (substitute y p (rename x z m))
  where
    z = fresh (used p `merge` used m `merge` [x, y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)

beta :: Term -> [Term]
beta (Apply (Lambda x m) n) =
  [substitute x n m]
    ++ [Apply (Lambda x m') n | m' <- beta m]
    ++ [Apply (Lambda x m) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply m n) =
  [Apply m' n | m' <- beta m]
    ++ [Apply m n' | n' <- beta n]

-- - - - - - - - - - - -- Normalize

normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms
    then return ()
    else normalize (head ms)

------------------------- Assignment 1: Combinators

infixl 5 :@

-- defining the combinator data type and all the combinator types that can be used in it

data Combinator = I | K | S | B | C | Q | R | X | Y | Z | Combinator :@ Combinator | V String

example1 :: Combinator
example1 = S :@ K :@ K :@ V "x"

example2 :: Combinator
example2 = S :@ (K :@ K) :@ I :@ V "x" :@ V "y"

-- - - - - - - - - - - -- show, parse

instance Show Combinator where
  show = f 0
    where
      f _ I = "I"
      f _ K = "K"
      f _ S = "S"
      f _ B = "B"
      f _ C = "C"
      f _ Q = "Q"
      f _ R = "R"
      f _ X = "X"
      f _ Y = "Y"
      f _ Z = "Z"
      f _ (V s) = s
      f i (c :@ d) = if i == 1 then "(" ++ s ++ ")" else s where s = f 0 c ++ " " ++ f 1 d

parse :: String -> Combinator
parse s = down [] s
  where
    down :: [Maybe Combinator] -> String -> Combinator
    down cs (' ' : str) = down cs str
    down cs ('(' : str) = down (Nothing : cs) str
    down cs ('I' : str) = up cs I str
    down cs ('K' : str) = up cs K str
    down cs ('S' : str) = up cs S str
    down cs ('B' : str) = up cs B str
    down cs ('C' : str) = up cs C str
    down cs ('Q' : str) = up cs Q str
    down cs ('R' : str) = up cs R str
    down cs ('X' : str) = up cs C str
    down cs ('Y' : str) = up cs Q str
    down cs ('Z' : str) = up cs R str
    down cs (c : str) = up cs (V [c]) str
    up :: [Maybe Combinator] -> Combinator -> String -> Combinator
    up [] c [] = c
    up (Just c : cs) d str = up cs (c :@ d) str
    up (Nothing : cs) d (')' : str) = up cs d str
    up cs d str = down (Just d : cs) str

-- - - - - - - - - - - -- step, run

-- function to peform all the steps for the combinator logic possible in one step, giving a list of all the possible results from that one step

step :: Combinator -> [Combinator]
step (I :@ x1) = concat [[x1], [I :@ x2 | x2 <- step (x1)]]
step (K :@ x1 :@ y1) = concat [[x1], [K :@ x1 :@ y2 | y2 <- step (y1)], [K :@ x2 :@ y1 | x2 <- step (x1)]]
step (S :@ x1 :@ y1 :@ z1) = concat [[x1 :@ z1 :@ (y1 :@ z1)], [S :@ x2 :@ y1 :@ z1 | x2 <- step (x1)], [S :@ x1 :@ y2 :@ z1 | y2 <- step (y1)], [S :@ x1 :@ y1 :@ z2 | z2 <- step (z1)]]
step (B :@ x1 :@ y1 :@ z1) = concat [[x1 :@ (y1 :@ z1)], [B :@ x2 :@ y1 :@ z1 | x2 <- step (x1)], [B :@ x1 :@ y2 :@ z1 | y2 <- step (y1)], [B :@ x1 :@ y1 :@ z2 | z2 <- step (z1)]]
step (C :@ x1 :@ y1 :@ z1) = concat [[(x1 :@ z1) :@ y1], [C :@ x2 :@ y1 :@ z1 | x2 <- step (x1)], [C :@ x1 :@ y2 :@ z1 | y2 <- step (y1)], [C :@ x1 :@ y1 :@ z2 | z2 <- step (z1)]]
step (Q :@ u1 :@ x1 :@ y1) = concat [[u1 :@ x1], [Q :@ u2 :@ x1 :@ y1 | u2 <- step (u1)], [Q :@ u1 :@ x2 :@ y1 | x2 <- step (x1)], [Q :@ u1 :@ x1 :@ y2 | y2 <- step (y1)]]
step (R :@ u1 :@ v1 :@ x1 :@ y1) = concat [[u1 :@ v1 :@ x1], [R :@ u2 :@ v1 :@ x1 :@ y1 | u2 <- step (u1)], [R :@ u1 :@ v2 :@ x1 :@ y1 | v2 <- step (v1)], [R :@ u1 :@ v1 :@ x2 :@ y1 | x2 <- step (x1)], [R :@ u1 :@ v1 :@ x1 :@ y2 | y2 <- step (y1)]]
step (X :@ u1 :@ x1 :@ y1 :@ z1) = concat [[u1 :@ x1 :@ (y1 :@ z1)], [X :@ u2 :@ x1 :@ y1 :@ z1 | u2 <- step (u1)], [X :@ u1 :@ x2 :@ y1 :@ z1 | x2 <- step (x1)], [X :@ u1 :@ x1 :@ y2 :@ z1 | y2 <- step (y1)], [X :@ u1 :@ x1 :@ y1 :@ z2 | z2 <- step (z1)]]
step (Y :@ u1 :@ x1 :@ y1 :@ z1) = concat [[u1 :@ (x1 :@ z1) :@ y1], [Y :@ u2 :@ x1 :@ y1 :@ z1 | u2 <- step (u1)], [Y :@ u1 :@ x2 :@ y1 :@ z1 | x2 <- step (x1)], [Y :@ u1 :@ x1 :@ y2 :@ z1 | y2 <- step (y1)], [Y :@ u1 :@ x1 :@ y1 :@ z2 | z2 <- step (z1)]]
step (Z :@ u1 :@ x1 :@ y1 :@ z1) = concat [[u1 :@ (x1 :@ z1) :@ (y1 :@ z1)], [Z :@ u2 :@ x1 :@ y1 :@ z1 | u2 <- step (u1)], [Z :@ u1 :@ x2 :@ y1 :@ z1 | x2 <- step (x1)], [Z :@ u1 :@ x1 :@ y2 :@ z1 | y2 <- step (y1)], [Z :@ u1 :@ x1 :@ y1 :@ z2 | z2 <- step (z1)]]
step (x1 :@ y1) = concat [[x2 :@ y1 | x2 <- step (x1)], [x1 :@ y2 | y2 <- step (y1)]]
step _ = []

-- function to completely reduce a combinator

run :: Combinator -> IO ()
run p = do
  print p
  let ps = step (p)
  if null ps
    then return ()
    else run (head ps)

------------------------- Assignment 2: Combinators to Lambda-terms

-- function to convert a combinatory expression to their lambda terms

toLambda :: Combinator -> Term
toLambda I = Lambda "x" (Variable "x")
toLambda K = Lambda "x" (Lambda "y" (Variable "x"))
toLambda S = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x") (Variable "z")) (Apply (Variable "y") (Variable "z")))))
toLambda B = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Variable "x") (Apply (Variable "y") (Variable "z")))))
toLambda C = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x") (Variable "z")) (Variable "z"))))
toLambda Q = Lambda "u" (Lambda "x" (Lambda "y" (Apply (Variable "u") (Variable "x"))))
toLambda R = Lambda "u" (Lambda "v" (Lambda "x" (Lambda "y" (Apply (Apply (Variable "u") (Variable "v")) (Variable "x")))))
toLambda X = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u") (Variable "x")) (Apply (Variable "y") (Variable "z"))))))
toLambda Y = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u") (Apply (Variable "x") (Variable "z"))) (Variable "y")))))
toLambda Z = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u") (Apply (Variable "x") (Variable "z"))) (Apply (Variable "y") (Variable "z"))))))
toLambda (c :@ d) = Apply (toLambda c) (toLambda d)
toLambda (V s) = Variable s

------------------------- Assignment 3: Lambda-terms to Combinators

-- function to abstract the correct combinatory expression

abstract :: Var -> Combinator -> Combinator
abstract x (a :@ b) = S :@ abstract x a :@ abstract x b
-- if statement to check for the two cases, and give the correct, case dependant output

abstract x (V c) =
  if c == x
    then I
    else K :@ V c
abstract x a = K :@ a

-- function to convert a lambda function into its corresponding combinatory logic

toCombinator :: Term -> Combinator
toCombinator (Variable x) = V x
toCombinator (Lambda x m) = abstract x (toCombinator m)
toCombinator (Apply a b) = toCombinator a :@ toCombinator b

------------------------- Assignment 4: Estimating growth

-- function to find the length of a lambda expression
sizeL :: Term -> Int
sizeL (Apply x m) = 1 + sizeL (x) + sizeL (m)
sizeL (Lambda x m) = 1 + sizeL (m)
sizeL (Variable x) = 1

-- function to find the length of a combinatory expression
sizeC :: Combinator -> Int
sizeC (a :@ b) = 1 + sizeC (a) + sizeC (b)
sizeC (a) = 1

-- a series that produces a linear increase in lambda expression growth but exponential in combinator length
series :: Int -> Term
series n
  | (n + 1) `rem` 3 == 0 =
      Lambda "z" (Apply (series (n - 1)) (Variable "z"))
  | (n + 2) `rem` 3 == 0 =
      Lambda "y" (Apply (series (n - 1)) (Variable "y"))
  | (n + 1) == 1 = Lambda "x" (Variable "x")
  | otherwise = Lambda "x" (Apply (series (n - 1)) (Variable "x"))

------------------------- Assignment 5: Optimised interpretation

data Complexity = Linear | Quadratic | Cubic | Exponential

-- function to find the number of free variables in a lambda expression

free :: Term -> [Var]
free (Apply x m) = free x ++ free m
free (Lambda x m) = filter (/= x) (free m)
free (Variable x) = [x]

-- function to see if a variable lacks any variables

novar :: Combinator -> Bool
novar (V x) = False
novar (x :@ y)
  | novar x == True && novar y == True =
      True
  | otherwise = False
novar x = True

-- function to abstract the correct combinatory expression

abst :: Var -> Combinator -> Combinator
-- function to work the most basic cases
abst x (V c)
  | c == x =
      I 
  | otherwise = Q :@ I :@ V c --(replaces the optimisation rule for K (x (V c) = K :@ V c))
  
-- function to work the cases involving three expressions, one of which contains no variables
abst x (k :@ a :@ b)
  | x `elem` free (toLambda (a)) && x `elem` free (toLambda (b)) && novar (k) == True =
      Z :@ k :@ abst x a :@ abst x b
  | x `elem` free (toLambda (a)) && x `notElem` free (toLambda (b)) && novar (k) == True =
      Y :@ k :@ abst x a :@ b
  | x `notElem` free (toLambda (a)) && x `elem` free (toLambda (b)) && novar (k) == True =
      X :@ k :@ a :@ abst x b
  | x `notElem` free (toLambda (a)) && x `notElem` free (toLambda (b)) && novar (k) == True =
      R :@ k :@ a :@ b
-- function to work the cases involving two expressions
abst x (a :@ b)
  | x `elem` free (toLambda (a)) && x `elem` free (toLambda (b)) =
      S :@ abst x a :@ abst x b
  | x `elem` free (toLambda (a)) && x `notElem` free (toLambda (b)) =
      C :@ abst x a :@ b
  | x `notElem` free (toLambda (a)) && x `elem` free (toLambda (b)) =
      B :@ a :@ abst x b
  | x `notElem` free (toLambda (a)) && x `notElem` free (toLambda (b)) =
      Q :@ a :@ b
-- function to work the remaining cases
abst x m = Q :@ I :@ m --(replaces the optimisation rule for K (x (V c) = K :@ V c))

-- function to convert a lambda function into its corresponding combinatory logic
comb :: Term -> Combinator
comb (Variable x) = V x
comb (Lambda x m) = abst (x) (comb (m))
comb (Apply a b) = comb (a) :@ comb (b)

-- function that claims the above expression as growing with quadratic complexity
claim :: Complexity
claim = Quadratic
