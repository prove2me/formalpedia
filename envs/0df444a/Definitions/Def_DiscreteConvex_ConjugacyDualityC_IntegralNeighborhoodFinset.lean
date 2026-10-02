-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntegralNeighborhoodFinset
-- name    : DiscreteConvex_ConjugacyDualityC_IntegralNeighborhoodFinset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:21.762721+00:00
-- url     : https://prove2.me/theorems/bd0b956d-8f5d-4102-bbd8-29a1e89efc1d
-- title:
--   IntegralNeighborhoodFinset
-- statement:
--   The integral neighborhood $N(x)$ of $x\in\mathbb R^V$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(x)` of `x ∈ Rⱽ`, as a finite set. -/
noncomputable def IntegralNeighborhoodFinset (x : V → ℝ) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc ⌊x v⌋ ⌈x v⌉)

end DiscreteConvex.ConjugacyDualityC


