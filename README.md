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

- Page 223:
  - A type class creates a Constraint! It's not a type, but restricts the type!
    ```
    ghci> :i Show
    type Show :: * -> Constraint     # type - actually its kind - of the type class Show
    class Show a where               # Show is a type class
      show :: a -> String

    ghci> :k Show
    Show :: * -> Constraint
    ```
  - Type classes are used as Constraints!
    ```
    getDirections :: ∀ a. (Show a, HasAddress a) => a -> Directions
    ```

- Page 225:
  - You can have multiple Constraints in a single Type Signature:  
    `getDirections :: ∀ a. Show a => HasAddress a => a -> Directions`
  - You can also define multiple Constraints using Parentheses separating the Typeclasses by commas:  
    `getDirections :: ∀ a. (Show a, HasAddress a) => a -> Directions`
  - Tip: Revert to the more verbose signature when type signature spans multiple lines:
    ```
    getDirections
    :: ∀ a
    . Show a
    => HasAddress a
    => a
    -> Directions
    ```
- Page 227:
  - Every typeclass method must have its polymorphic parameter in its type signature.

- Page 237:
  - Deriving `Show` instances:
    ```
    import Data.Generic.Rep (class Generic)
    import Data.Show.Generic (genericShow)

    derive instance genericSomeType :: Generic SomeType _

    instance showSomeType :: Show SomeType where
      show = genericShow
    ```

- Page 244:
  - Instance Chaining:
    ```
    class IsRecord a where
      isRecord :: a -> Boolean

    instance isRecordRecord :: IsRecord (Record a) where
      isRecord _ = true
    else instance isRecordOther :: IsRecord a where ❶
      isRecord _ = false
    ```

- Page 245:
  - Orphaned Instances
  - What we need is an authoritative Definition and there really is only two places of authority:
    - the module where the typeclass is defined and
    - the module where the type is defined.
  - We need a way to control either the Typeclass or the Type.
    - You can use Newtypes for data types you don't control.

- Page 250:
  - [Fundeps/Functions Dependencies](https://stackoverflow.com/a/20040343/365425)
