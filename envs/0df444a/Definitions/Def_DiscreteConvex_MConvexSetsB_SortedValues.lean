-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
-- name    : DiscreteConvex_MConvexSetsB_SortedValues
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:42.418416+00:00
-- url     : https://prove2.me/theorems/41582187-f7d7-4580-8302-22845c3be574
-- title:
--   SortedValues
-- statement:
--   The distinct values of $p : V \to \mathbb R$, sorted in decreasing order: $\hat p_1 > \hat p_2 > \cdots > \hat p_m$ (Eq. (4.4)), the first ingredient of the Lovász extension.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, Eq. (4.4): the distinct values of a
vector `p`, sorted in decreasing order, in `DiscreteConvex.MConvexSetsB`. Supports the Lovász
extension (Eq. (4.6), Proposition 4.5, Theorem 4.16).
-/

namespace DiscreteConvex.MConvexSetsB

open Classical in
/-- The distinct values of `p : V → R`, sorted in decreasing order: `p̂₁ > p̂₂ > ⋯ > p̂ₘ`
(Eq. (4.4)). -/
noncomputable def SortedValues {V : Type*} [Fintype V] (p : V → ℝ) : List ℝ :=
  (Finset.image p Finset.univ).sort (· ≥ ·)

end DiscreteConvex.MConvexSetsB


