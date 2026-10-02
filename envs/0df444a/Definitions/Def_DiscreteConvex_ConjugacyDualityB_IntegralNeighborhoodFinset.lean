-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntegralNeighborhoodFinset
-- name    : DiscreteConvex_ConjugacyDualityB_IntegralNeighborhoodFinset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:17.749735+00:00
-- url     : https://prove2.me/theorems/5954c26b-2f8c-4365-b048-a80cf509a1bc
-- title:
--   IntegralNeighborhoodFinset
-- statement:
--   The integral neighborhood $N(x)$ of $x\in\mathbb R^V$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99, Eq. (3.58)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(x)` of `x ∈ Rⱽ`. -/
noncomputable def IntegralNeighborhoodFinset (x : V → ℝ) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc ⌊x v⌋ ⌈x v⌉)

end DiscreteConvex.ConjugacyDualityB


