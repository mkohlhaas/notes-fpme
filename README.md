Page 98:
- We can freely move Parameters across the equals sign as long as we move the rightmost Parameter first
and maintain the correct order:
```
f1 x y z = x + y z
f2 x y   = \z -> x y z
f3 x     = \y z -> x y z
f4       = \x y z -> x y z
```

- Remember that Type Signatures are Right-Associative which means they have implied Parentheses on the
right. This means that the Parentheses on `(a -> c)` are redundant and we can remove them:
```
compose :: ∀ a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
```

p. 101
- This syntax looks odd at first:
```
\person -> person { age = 18 }
_ { age = 18 }
```

Chapter 5
- flip apply:
  - flip: (a' → b' → c') → b' → a' → c'
  - apply: (a → b) → a → b
  - flip apply:
    - (a' → b' → c') = (a → b) → a → b
    - f = (a → b) = a'
    - a = b'
    - b = c'
    - ⇒ (into) flip: (f → a → b) → (a → f → b)

- Page 182: 5.25. Local Function Type Signatures
  - cp. Haskell's {-# LANGUAGE ScopedTypeVariables #-}

- Page 184: Natural transformation (e.g. `reverse`)
- Page 190: `filter` filters in - not out!
- Page 194: Point-free
  - Remember, composition only works with Functions waiting for a single Parameter.
  - `f $ g a` ≡ `f <<< g`
  - In Haskell the same but also: `f $ g a` ≡ `f . g`

- Page 207/213: Recursion "trick":
  - `takeEnd`
  - `dropEnd`
  - `unzip`
