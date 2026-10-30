-- Prove2me | Definitions.Def_NAPPAL_VPEB_Lam
-- name    : NAPPAL_VPEB_Lam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:48.629884+00:00
-- url     : https://prove2.me/theorems/6d3c5749-0cb1-495a-84f3-3b4bedddcdba
-- title:
--   The potential $\Lambda^k$ of (18)
-- statement:
--   For a sequence $w^k$ and $k \ge 1$,
--   $$\Lambda^k = \mathcal L_\gamma(u^k,v^k,p^k) + c_1\|u^{k-1} - u^k\|^2 + c_2\|v^{k-1} - v^k\|^2 + \frac{1}{2\gamma}\|p^{k-1} - p^k\|^2 .$$
--   It is the Lyapunov function of the convergence analysis: Lemma 4.3 shows that it decreases by $c_3\|w^k - w^{k+1}\|^2$ per step.
--
--   **Formalization Note** $\Lambda^k$ uses $w^{k-1}$ and is used only for $k \ge 1$; Lean's value at $k = 0$ is $\mathcal L_\gamma(w^0)$, which no statement uses.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, p. 14, eq. (18)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_W
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params
import Definitions.Def_NAPPAL_VPEB_augLag
import Definitions.Def_NAPPAL_VPEB_c1
import Definitions.Def_NAPPAL_VPEB_c2

namespace NAPPAL.VPEB

/-- **The potential `Λ^k` of (18).**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, p. 14, eq. (18): "Λ^k := Lγ(u^k, v^k, p^k) + c1‖u^{k−1} − u^k‖² + c2‖v^{k−1} − v^k‖²
+ (1/(2γ))‖p^{k−1} − p^k‖²".

`Lam P A w k = L_γ(u^k, v^k, p^k) + c₁‖u^{k−1} − u^k‖² + c₂‖v^{k−1} − v^k‖²
+ (1/(2γ))‖p^{k−1} − p^k‖²` in `(−∞, +∞]`.

**Formalization Note.** `Λ^k` uses `w^{k−1}` and is defined by the paper for `k ≥ 1`
(paper.md Reading 8); every statement of the mission uses `Lam P A w k` only under `1 ≤ k`.
At `k = 0` Lean's `0 − 1 = 0` makes the value `L_γ(w⁰)`, a junk value that is never used. -/
noncomputable def Lam {n d m : ℕ} (P : Problem n d m) (A : Params n) (w : ℕ → W n d m)
    (k : ℕ) : EReal :=
  augLag P A.γ (w k).fst.fst (w k).fst.snd (w k).snd +
    ((c1 P A * ‖(w (k - 1)).fst.fst - (w k).fst.fst‖ ^ 2 +
      c2 P A * ‖(w (k - 1)).fst.snd - (w k).fst.snd‖ ^ 2 +
      1 / (2 * A.γ) * ‖(w (k - 1)).snd - (w k).snd‖ ^ 2 : ℝ) : EReal)

end NAPPAL.VPEB


