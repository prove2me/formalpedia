-- Prove2me | Definitions.Def_NAPPAL_VPEB_Assumption1
-- name    : NAPPAL_VPEB_Assumption1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:08.592471+00:00
-- url     : https://prove2.me/theorems/7b59e105-a9e4-4ae4-b36f-98350bec8578
-- title:
--   Assumption 1 and the standing hypotheses of (P)
-- statement:
--   An instance of (P) satisfies **Assumption 1** (together with the standing hypotheses of §1.1) if:
--
--   1. $U$ is closed and convex, and $\Theta$ is differentiable;
--   2. (H1) $G$ is differentiable on $\mathbb{R}^n \times \mathbb{R}^d$ and $\|\nabla G(x) - \nabla G(y)\| \le L_G \|x - y\|$;
--   3. (H2) $H$ is differentiable on $\mathbb{R}^d$ and $\|\nabla H(x) - \nabla H(y)\| \le L_H \|x - y\|$;
--   4. (H3) $J$ never takes the value $-\infty$, is lower semicontinuous on $\operatorname{dom} J$, $\operatorname{dom} J$ is convex when $U = \mathbb{R}^n$, $J$ is locally Lipschitz on $\operatorname{dom} J \cap U$, and $\operatorname{dom} J \cap U \ne \emptyset$;
--   5. (H4) $\|\Theta(u) - \Theta(u')\| \le L^0_\Theta \|u - u'\|$ for all $u, u'$;
--   6. (H5) each component $\Omega_j$ is differentiable with $L_{\Omega_j}$-Lipschitz gradient; one writes $L_\Omega = \sum_j L_{\Omega_j}$;
--   7. (H6) $\operatorname{Im}\Theta \subseteq \operatorname{Im} B$, and $B$ has full column rank: $\lambda_{\min}(B^\top B) > 0$;
--   8. (H7) $F$ is bounded below and coercive on the feasible set $\{(u,v) : \Theta(u) + Bv = 0\}$: for every $M$ there is $R$ with $F(u,v) \ge M$ whenever $\Theta(u) + Bv = 0$ and $\|(u,v)\| \ge R$.
--
--   All Lipschitz constants are nonnegative.
--
--   **Formalization Note** $G$ and $H$ are real-valued on the whole space (the declaration of p. 2), so "Lipschitz on dom" in (H1)–(H2) is global. "Tall" in (H6) and the "full column rank of $B$ in (H6)" used on p. 14 are encoded as $\lambda_{\min}(B^\top B) > 0$. $\operatorname{dom} J \cap U \ne \emptyset$ is the properness of $J + I_U$. The feasible set in (H7) is the printed one, without $u \in U$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §1.1, p. 2 and Assumption 1 (H1)–(H7), p. 7

import Mathlib
import Definitions.Def_NAPPAL_VPEB_UV
import Definitions.Def_NAPPAL_VPEB_lamMin
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Problem_Theta
import Definitions.Def_NAPPAL_VPEB_Problem_F

namespace NAPPAL.VPEB

/-- **Assumption 1 together with the standing hypotheses of (P).**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §1.1, p. 2 (U closed convex; Θ differentiable; B an m × d tall matrix) and Assumption 1,
p. 7:
"(H1) G : Rn × Rd → (−∞, +∞] is a nonconvex differentiable function with dom(G) convex and with
its gradient ∇G being LG-Lipschitz continuous on dom(G).
(H2) H : Rd → (−∞, +∞] is a nonconvex differentiable function with dom(H) convex and with its
gradient ∇H being LH-Lipschitz continuous on dom(H).
(H3) J : Rn → (−∞, ∞] is l.s.c. on dom(J), and dom(J) is a convex set when U = Rn; J is local
Lipschitz continuous on dom(J) ∩ U when U is closed convex set of Rn.
(H4) Θ : Rn → Rm is L0Θ-Lipschitz continuous, i.e., ‖Θ(u) − Θ(u′)‖ ≤ L0Θ‖u − u′‖, ∀u, u′.
(H5) Ω(u) = (Ω1(u), ..., Ωm(u))⊤, function Ωj : Rn → R, has LΩj-Lipschitz gradient,
j = 1, ..., m, and denote LΩ := Σ_{j=1}^m LΩj.
(H6) B ∈ Rm×d is a tall matrix, and the image of Θ is contained in that of B, i.e.
Im(Θ) ⊆ Im(B).
(H7) F is lower bounded and coercive over the feasible set {(u, v) ∈ Rn × Rd : Θ(u) + Bv = 0}."

The fields: `U` closed and convex; `Θ` differentiable; (H1) `G` differentiable with
`L_G`-Lipschitz gradient on `ℝⁿ × ℝᵈ`; (H2) `H` differentiable with `L_H`-Lipschitz gradient;
(H3) `J` never `−∞`, l.s.c. on `dom J`, `dom J` convex when `U = ℝⁿ`, `J` locally Lipschitz on
`dom J ∩ U`, and `dom J ∩ U ≠ ∅`; (H4) `Θ` is `L⁰_Θ`-Lipschitz; (H5) each `Ω_j` is differentiable
with `L_{Ω_j}`-Lipschitz gradient; (H6) `Im Θ ⊆ Im B` and `λ_min(BᵀB) > 0`; (H7) `F` is bounded
below and coercive on `{(u, v) : Θ(u) + Bv = 0}`. All Lipschitz constants are nonnegative.

**Formalization Note.**
1. (H1), (H2): `G`, `H` are real-valued on all of `ℝⁿ × ℝᵈ`, `ℝᵈ`, as declared on p. 2
   (paper.md Reading 2), so "on dom(G)" is "everywhere".
2. (H3): `dom J = {u | J u ≠ ⊤}`; local Lipschitz continuity is that of the real function
   `u ↦ J(u)` on `dom J ∩ U`, where `J` is finite. `J_proper` (`dom J ∩ U ≠ ∅`) is the
   properness of `J + I_U` used by Definitions 2.1, 6.1 and by (12)–(14) (paper.md Reading 7).
3. (H6): "tall" and the "full column rank of B in (H6)" invoked on p. 14 are encoded as
   `0 < lamMin P.B` (paper.md Reading 6); Assumption 2(ii) divides by this number.
4. (H7): coercivity is `F(u, v) → +∞` as `‖(u, v)‖ → ∞` within the feasible set. The feasible
   set is `{Θ(u) + Bv = 0}` as printed (without `u ∈ U`).
5. Lipschitz constants are nonnegative real numbers; this only excludes meaningless negative
   "constants" when a space is trivial. -/
structure Assumption1 {n d m : ℕ} (P : Problem n d m) : Prop where
  U_closed : IsClosed P.U
  U_convex : Convex ℝ P.U
  Theta_differentiable : Differentiable ℝ P.Theta
  G_differentiable : Differentiable ℝ P.G
  LG_nonneg : 0 ≤ P.LG
  G_gradient_lipschitz : ∀ x y : UV n d, ‖gradient P.G x - gradient P.G y‖ ≤ P.LG * ‖x - y‖
  H_differentiable : Differentiable ℝ P.H
  LH_nonneg : 0 ≤ P.LH
  H_gradient_lipschitz : ∀ x y : EuclideanSpace ℝ (Fin d),
    ‖gradient P.H x - gradient P.H y‖ ≤ P.LH * ‖x - y‖
  J_ne_bot : ∀ u, P.J u ≠ ⊥
  J_lsc_on_dom : LowerSemicontinuousOn P.J {u | P.J u ≠ ⊤}
  J_dom_convex : P.U = Set.univ → Convex ℝ {u | P.J u ≠ ⊤}
  J_locally_lipschitz : LocallyLipschitzOn ({u | P.J u ≠ ⊤} ∩ P.U) (fun u => (P.J u).toReal)
  J_proper : ∃ u ∈ P.U, P.J u ≠ ⊤
  L0Θ_nonneg : 0 ≤ P.L0Θ
  Theta_lipschitz : ∀ u u' : EuclideanSpace ℝ (Fin n),
    ‖P.Theta u - P.Theta u'‖ ≤ P.L0Θ * ‖u - u'‖
  LΩj_nonneg : ∀ j, 0 ≤ P.LΩj j
  Omega_differentiable : ∀ j, Differentiable ℝ (fun u => P.Ω u j)
  Omega_gradient_lipschitz : ∀ j, ∀ x y : EuclideanSpace ℝ (Fin n),
    ‖gradient (fun u => P.Ω u j) x - gradient (fun u => P.Ω u j) y‖ ≤ P.LΩj j * ‖x - y‖
  range_Theta_subset : Set.range P.Theta ⊆ Set.range P.B
  lamMin_pos : 0 < lamMin P.B
  F_bddBelow : ∃ c : ℝ, ∀ u v, P.Theta u + P.B v = 0 → (c : EReal) ≤ P.F u v
  F_coercive : ∀ M : ℝ, ∃ R : ℝ, ∀ u v, P.Theta u + P.B v = 0 →
    R ≤ ‖(WithLp.toLp 2 (u, v) : UV n d)‖ → (M : EReal) ≤ P.F u v

end NAPPAL.VPEB


