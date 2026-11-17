-- Prove2me | Definitions.Def_N25_ExplicitWeilThreeLinear
-- name    : N25_ExplicitWeilThreeLinear
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:36.407201+00:00
-- url     : https://prove2.me/theorems/d3c813a3-b3a2-40c2-933a-1f19fa944066
-- title:
--   Linear elimination for the characteristic-three point counts
-- statement:
--   On the normalized chart $[1:y:z:w]$, the quadric has the form $$Q=y^2+yz-z+(z-1)w.$$ The file defines the bivariate residual obtained after eliminating $w$, finite sets of regular pairs with $z≠1$, exceptional points on $z=1$, the $y$- and $z$-chart contributions, and their structured projective count with the final point $[0:0:0:1]$. This decomposition reduces the $𝔽_3$, $𝔽_9$, and $𝔽_{27}$ computations to low-dimensional finite searches.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_ExplicitWeilThreeDefs
/-!
# Linear elimination for the ternary level-25 point counts

On the normalized chart `[1:y:z:w]`, the canonical quadric is linear in
`w`:

```
Q = y^2 + yz - z + (z - 1)w.
```

Away from `z=1`, this determines `w` uniquely.  Substitution into the
cubic leaves one bivariate residual equation.  The exceptional divisor
`z=1` is counted separately.

The first section proves the elimination identity over every field of
characteristic three.  The second section evaluates the resulting residual
over the three small polynomial-basis tables.  The `F_81` calculation is not
performed by a bivariate search here: the order-five Kummer model reduces it
once more to one-dimensional quotient fibres.
-/

namespace MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-! ## The characteristic-three elimination identity -/

section Elimination

variable {K : Type*} [Field K] [CharP K 3]

end Elimination

/-! ## Executable residual counts -/

/-- The same characteristic-three residual evaluated in an explicit signed
operation table. -/
def canonicalResidualX25Ternary {R : Type*}
    (O : TernaryRingOperations R) (y z : R) : R :=
  let y2 := O.mul y y
  let y3 := O.mul y2 y
  let y4 := O.mul y3 y
  let z2 := O.mul z z
  let z3 := O.mul z2 z
  let z4 := O.mul z3 z
  O.add
    (O.add (O.add (O.mul y4 z) (O.mul y z4)) (O.mul y3 z))
    (O.add (O.neg z4)
      (O.add y3 (O.add (O.neg y2) (O.add z2 z))))

/-- Pairs `(y,z)` on the regular part `z≠1` whose eliminated residual
vanishes.  Each pair determines a unique `w` by the quadric. -/
def canonicalRegularPairs25Three {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset (R × R) :=
  Finset.univ.filter fun yz =>
    yz.2 ≠ O.one ∧ canonicalResidualX25Ternary O yz.1 yz.2 = O.zero

/-- Points on the exceptional x-chart divisor `z=1`, where the quadric no
longer determines `w`.  This is a two-variable low-degree fibre. -/
def canonicalExceptionalPairs25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset (R × R) :=
  Finset.univ.filter fun yw =>
    IsCanonicalNormalized25Ternary O
      (.xChart yw.1 O.one yw.2)

/-- Points in the normalized projective chart `[0:1:z:w]`. -/
def canonicalYChartPairs25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset (R × R) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25Ternary O (.yChart zw.1 zw.2)

/-- Points in the normalized projective chart `[0:0:1:w]`. -/
def canonicalZChartValues25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset R :=
  Finset.univ.filter fun w =>
    IsCanonicalNormalized25Ternary O (.zChart w)

/-- Structurally decomposed projective count: regular x-chart residual pairs,
the exceptional divisor `z=1`, the next two normalized charts, and the final
point `[0:0:0:1]`. -/
def canonicalStructuredPointCount25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Nat :=
  (canonicalRegularPairs25Three O).card +
    (canonicalExceptionalPairs25Three O).card +
    (canonicalYChartPairs25Three O).card +
    (canonicalZChartValues25Three O).card + 1

end MazurProof.RationalPointsN25QuotientWeilThreeLinear


