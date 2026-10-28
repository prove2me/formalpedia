-- Prove2me | Definitions.Def_D1Bound5_IsD1Tuple
-- name    : D1Bound5_IsD1Tuple
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T21:23:55.290544+00:00
-- url     : https://prove2.me/theorems/59498c67-3453-48cd-9618-c35fa611af60
-- title:
--   Ordered Diophantine tuples in a commutative ring
-- statement:
--   Let $R$ be a commutative ring and let $n$ be a nonnegative integer. A map $f:\{0,\ldots,n-1\}\to R$ is a Diophantine tuple if it is injective, all its entries are nonzero, and
--
--   $$\forall i\ne j,\quad \exists r\in R,\quad r^2=f(i)f(j)+1.$$
--
--   The index order records an enumeration; this definition imposes no monotonicity condition. It provides the tuple formulation used when passing from finite Diophantine sets to ordered sextuples.
-- source:
--   https://github.com/tomislav-math/d1-bound5-lean/blob/a019c2a2b8e7a40dcf88c9d119d225cce84a61df/D1Bound5/Basic.lean#L18-L21

import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Basic

namespace D1Bound5






/-- The indexed form of a tuple, before imposing an order. -/
def IsD1Tuple {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R) : Prop :=
  Function.Injective f ∧ (∀ i, f i ≠ 0) ∧
  ∀ i j, i ≠ j → ∃ r : R, r * r = f i * f j + 1





end D1Bound5


