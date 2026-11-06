-- Prove2me | Definitions.Def_AnytimeAdaVR_dReport
-- name    : AnytimeAdaVR_dReport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:43.62593+00:00
-- url     : https://prove2.me/theorems/910baf52-f17e-46f2-96f4-4849e3a4bc9b
-- title:
--   Report $R_{D,N}$ of the D path
-- statement:
--   Local query $r$ of the D path is labelled by its pre-update point $x_{r-1}$. The report after $N\ge1$ queries is
--   $$
--   R_{D,N}=x_{R(N)-1},
--   $$
--   a reservoir sample of $x_0,\dots,x_{N-1}$ with coins independent of the gradient stream.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), Algorithm 3, p.9; App. D, p.24

import Mathlib
import Definitions.Def_AnytimeAdaVR_dSeq
import Definitions.Def_AnytimeAdaVR_reservoirIndex

namespace AnytimeAdaVR

/-- **The report `R_{D,N}` of the D path after `N` local queries.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), Algorithm 3, p.9: "Save
y ← x and query u ← g(y; ξ_t) … t ← t + 1. With probability 1/t, set R ← y using an independent coin",
and App. D, p.24: "After N ≥ 1 completed local queries, the report R_{D,N} is a uniformly sampled
member of x_0, …, x_{N−1}, maintained by reservoir sampling with coins independent of the gradient
stream."

The label of local query `r` is the pre-update point `x_{r−1}`, so the report is
`x_{reservoirIndex U N − 1}`. -/
noncomputable def dReport {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ξ) (U : ℕ → unitInterval) (N : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  (dSeq g xinit ξ (reservoirIndex U N - 1)).1

end AnytimeAdaVR


