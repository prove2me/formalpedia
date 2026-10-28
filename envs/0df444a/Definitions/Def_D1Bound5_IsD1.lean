-- Prove2me | Definitions.Def_D1Bound5_IsD1
-- name    : D1Bound5_IsD1
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T15:04:11.236222+00:00
-- url     : https://prove2.me/theorems/c45f56c0-f653-4ec2-94e5-d0eeda056120
-- title:
--   $D(1)$-sets in a commutative ring
-- statement:
--   Let $R$ be a commutative ring with identity and let $A$ be a finite subset of $R$. The set $A$ has property $D(1)$ if every element of $A$ is nonzero and
--   $$
--   \forall a,b\in A,\quad a\ne b\ \Longrightarrow\ \exists r\in R,\quad r^2=ab+1.
--   $$
--   Zero is allowed as a square value. This predicate gives the finite-set formulation of a Diophantine tuple.
-- source:
--   https://github.com/tomislav-math/d1-bound5-lean/blob/1fe0adf1028af0e41ea578660c8d48875cde6588/D1Bound5/Basic.lean#L7-L10

import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false

namespace D1Bound5

/-- Distinct nonzero entries; zero is permitted as a square value. -/
def IsD1 {R : Type*} [CommRing R] (A : Finset R) : Prop :=
  (∀ x ∈ A, x ≠ 0) ∧
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ r : R, r * r = x * y + 1










end D1Bound5


