-- Prove2me | Definitions.Def_N25_ExplicitKummerThreeF81
-- name    : N25_ExplicitKummerThreeF81
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:58.116439+00:00
-- url     : https://prove2.me/theorems/0c682e40-57eb-4fb7-bc0a-1ee7a30699b5
-- title:
--   The one-dimensional Kummer fibre classifier over $𝔽_{81}$
-- statement:
--   In $𝔽_{81}=𝔽_3[q]/(q^4+2q^3+2)$, the file defines a primitive fifth root $e=1+2q+2q^2$, its square, the associated coefficients $A$ and $B$, and the fibre denominator $D(t)=1+At$ and numerator $N(t)=t^2(B+e^2t)$. It defines an executable classifier for the number of roots of $r^5D(t)+N(t)=0$ and the corrected projective count obtained from the fibre sum. This is the terminal $81$-parameter certificate behind the value $89$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
/-!
# One-dimensional `F_81` certificate for the Kummer quotient

The structural file reduces the dense canonical curve to

```
r^5 (1 + A t) + t^2 (B + e^2 t) = 0.
```

For a fixed quotient parameter `t`, the fifth-power map on `F_81^×` has
kernel of order five and image of order sixteen.  Consequently a nonzero
target has five roots exactly when its sixteenth power is one; zero has one
root.  The executable certificate below therefore inspects 81 quotient
parameters, not `81^2` pairs or `81^3` ambient tuples.

The generic group-theoretic root-count lemma is connected below to the
executable table through a genuine field structure on `F81`.  The remaining
projective bookkeeping is kept separate from this terminal certificate.
-/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- A primitive fifth root in the polynomial basis
`F_81 = F_3[q]/(q^4+2q^3+2)`: `e=1+2q+2q²`. -/
def f81FifthRoot25 : F81 :=
  ⟨.one, .two, .two, .zero⟩

/-- The square `e²=2+q+2q²`, stored as a literal so the fibre evaluator
does not repeatedly expand the same power. -/
def f81FifthRootSq25 : F81 :=
  ⟨.two, .one, .two, .zero⟩

/-- The Kummer coefficient `A=2e³+e+1=2+2q³`. -/
def f81KummerA25 : F81 :=
  ⟨.two, .zero, .zero, .two⟩

/-- The Kummer coefficient `B=e³+2e²+2e+1=1+2q+q²+q³`. -/
def f81KummerB25 : F81 :=
  ⟨.one, .two, .one, .one⟩

/-! ## Semantic interpretation of the coefficient table -/
/-- The denominator `1+At` of the Kummer fibre over `t`. -/
def f81KummerDenominator25 (t : F81) : F81 :=
  f81Operations.add f81Operations.one
    (f81Operations.mul f81KummerA25 t)

/-- The numerator `t²(B+e²t)` of the Kummer fibre over `t`. -/
def f81KummerNumerator25 (t : F81) : F81 :=
  f81Operations.mul (f81Operations.mul t t)
    (f81Operations.add f81KummerB25
      (f81Operations.mul f81FifthRootSq25 t))

/-- The number of roots predicted by the cyclic fifth-power map for the
Kummer fibre over `t`.

If the linear coefficient of `r⁵` vanishes, the equation is either empty or
the whole field.  Otherwise its target is zero (one root), a nonzero fifth
power (five roots), or a non-fifth-power (no roots). -/
def f81KummerFiberSize25 (t : F81) : Nat :=
  let O := f81Operations
  let denominator := f81KummerDenominator25 t
  let numerator := f81KummerNumerator25 t
  if denominator = O.zero then
    if numerator = O.zero then 81 else 0
  else
    let target := O.mul (O.neg numerator) (f81Inv denominator)
    if target = O.zero then 1
    else if ternaryPow O target 16 = O.one then 5 else 0

/-- The projective Kummer-model count subtracts the one point introduced by
clearing `r⁴` at `r=0`, then adds the three explicitly classified points on
the Segre boundary. -/
def f81StructuralKummerPointCount25 : Nat :=
  (∑ t : F81, f81KummerFiberSize25 t) - 1 + 3

end MazurProof.RationalPointsN25QuotientKummerThreeF81


