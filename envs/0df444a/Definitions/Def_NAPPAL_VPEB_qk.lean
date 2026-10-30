-- Prove2me | Definitions.Def_NAPPAL_VPEB_qk
-- name    : NAPPAL_VPEB_qk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:09:40.839426+00:00
-- url     : https://prove2.me/theorems/98b16568-fe63-46e2-b63b-6a6564718e08
-- title:
--   The vector $q^k = p^k + \gamma(\Theta(u^k) + Bv^k)$
-- statement:
--   For a sequence $w^k = (u^k, v^k, p^k)$ and penalty parameter $\gamma$,
--   $$q^k = p^k + \gamma\,(\Theta(u^k) + Bv^k) \in \mathbb{R}^m .$$
--   It is the multiplier estimate with which NAPP-AL linearizes the augmented term in steps (5) and (6).
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, NAPP-AL box, p. 8

import Mathlib
import Definitions.Def_NAPPAL_VPEB_W
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Problem_Theta
import Definitions.Def_NAPPAL_VPEB_Params

namespace NAPPAL.VPEB

/-- **The vector `q^k = p^k + γ(Θ(u^k) + Bv^k)` of NAPP-AL.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, NAPP-AL box, p. 8: "Set q^k = p^k + γ(Θ(u^k) + Bv^k)".

For a sequence `w : ℕ → W n d m`, `qk P A w k = p^k + γ(Θ(u^k) + Bv^k)` with
`(u^k, v^k, p^k) = w k`. -/
noncomputable def qk {n d m : ℕ} (P : Problem n d m) (A : Params n) (w : ℕ → W n d m)
    (k : ℕ) : EuclideanSpace ℝ (Fin m) :=
  (w k).snd + A.γ • (P.Theta (w k).fst.fst + P.B (w k).fst.snd)

end NAPPAL.VPEB


