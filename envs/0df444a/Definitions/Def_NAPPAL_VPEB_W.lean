-- Prove2me | Definitions.Def_NAPPAL_VPEB_W
-- name    : NAPPAL_VPEB_W
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:24.295992+00:00
-- url     : https://prove2.me/theorems/854fd418-a9b7-4aaa-98e1-fba0265074a6
-- title:
--   The Euclidean space $\mathbb{R}^n \times \mathbb{R}^d \times \mathbb{R}^m$ of points $w = (u,v,p)$
-- statement:
--   The **primal–dual space** is $\mathbb{R}^n \times \mathbb{R}^d \times \mathbb{R}^m$, whose points are written $w = (u, v, p)$: $u$ and $v$ are the primal variables of problem (P) and $p$ is the multiplier of the constraint $\Theta(u) + Bv = 0$. It carries the Euclidean norm
--   $$\|w\|^2 = \|u\|^2 + \|v\|^2 + \|p\|^2 .$$
--
--   The iterates $w^k$ of NAPP-AL, the augmented Lagrangian $\mathcal L_\gamma(w)$ and its subdifferential live on this space.
--
--   **Formalization Note** The space is `WithLp 2 (WithLp 2 (ℝⁿ × ℝᵈ) × ℝᵐ)`; $u$, $v$, $p$ are `w.fst.fst`, `w.fst.snd`, `w.snd`.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §2, pp. 5–6 (w = (u, v, p); Euclidean norm)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_UV

namespace NAPPAL.VPEB

/-- **The Euclidean space `ℝⁿ × ℝᵈ × ℝᵐ` of primal-dual points `w = (u, v, p)`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §2, p. 6 ("with w = (u, v, p)") and p. 5 (Euclidean scalar product and Euclidean norm).

A point `w : W n d m` has primal part `w.fst : UV n d`, i.e. `u = w.fst.fst ∈ ℝⁿ` and
`v = w.fst.snd ∈ ℝᵈ`, and dual part `p = w.snd ∈ ℝᵐ`.

**Formalization Note.** Both products are `WithLp 2`, so
`‖w‖² = ‖u‖² + ‖v‖² + ‖p‖²` (proved in `Solutions/verification/NAPPAL_VPEB_sanity.lean`) and the
inner product is the sum of the three Euclidean inner products. -/
abbrev W (n d m : ℕ) : Type :=
  WithLp 2 (UV n d × EuclideanSpace ℝ (Fin m))

end NAPPAL.VPEB


