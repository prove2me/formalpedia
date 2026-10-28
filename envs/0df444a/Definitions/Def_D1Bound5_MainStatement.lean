-- Prove2me | Definitions.Def_D1Bound5_MainStatement
-- name    : D1Bound5_MainStatement
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T15:04:23.792985+00:00
-- url     : https://prove2.me/theorems/ffbfc684-901b-4e85-94ab-70088a3a9525
-- title:
--   Uniform bound of five in imaginary quadratic integer rings
-- statement:
--   The proposition that, for every imaginary quadratic number field $K$ and every finite $D(1)$-set $A$ in its full ring of integers $\mathcal O_K$,
--   $$
--   |A|\le 5.
--   $$
--   Here $K$ is a number field of degree two over $\mathbb Q$ with no real embedding. The $D(1)$ condition requires nonzero entries and, for each pair of distinct entries $a,b$, a square root of $ab+1$ in $\mathcal O_K$. This definition names the proposition asserted by the main theorem.
-- source:
--   https://github.com/tomislav-math/d1-bound5-lean/blob/1fe0adf1028af0e41ea578660c8d48875cde6588/D1Bound5/Specification.lean#L10-L16

import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Basic
import Definitions.Def_D1Bound5_IsD1
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

open scoped NumberField

universe u

set_option autoImplicit false

namespace D1Bound5

/-- The requested theorem as a proposition, not an asserted theorem.
`RingOfIntegers` is mathlib's full integral closure of the integers.
Degree two and totally complex specify an imaginary quadratic number field. -/
def MainStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K],
    Module.finrank ℚ K = 2 →
    ∀ A : Finset (𝓞 K), IsD1 A → A.card ≤ 5





end D1Bound5


