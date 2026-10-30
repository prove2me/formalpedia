-- Prove2me | Definitions.Def_NAPPAL_VPEB_Ltil
-- name    : NAPPAL_VPEB_Ltil
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:08:51.472113+00:00
-- url     : https://prove2.me/theorems/41db864d-8e1c-42e8-91ff-3de9d2b5c1be
-- title:
--   $\tilde{\mathcal L}_\gamma = \mathcal L_\gamma + I_U$
-- statement:
--   For an instance of (P) and $\gamma \in \mathbb{R}$, define on $\mathbb{R}^n \times \mathbb{R}^d \times \mathbb{R}^m$
--   $$\tilde{\mathcal L}_\gamma(w) = \mathcal L_\gamma(u,v,p) + I_U(u) = \begin{cases} \mathcal L_\gamma(u,v,p), & u \in U, \\ +\infty, & u \notin U. \end{cases}$$
--
--   The paper's $\partial \mathcal L_\gamma(w)$ (in Proposition 3.1, Theorem 4.1(iv), and the KL property of Proposition 6.1) is the limiting subdifferential of this function: the stationarity display on p. 6 carries the normal cone block $\mathcal N_U(u) = \partial I_U(u)$.
--
--   **Formalization Note** At the iterates $w^{k+1}$ (where $u^{k+1} \in U$) and at their accumulation points ($U$ is closed), $\tilde{\mathcal L}_\gamma$ equals $\mathcal L_\gamma$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §2, p. 6 (augmented Lagrangian and the stationarity display with N_U(u)); Definition 2.1(iv), p. 6

import Mathlib
import Definitions.Def_NAPPAL_VPEB_W
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_augLag

namespace NAPPAL.VPEB

/-- **`L̃_γ = L_γ + I_U`, the augmented Lagrangian with the constraint `u ∈ U`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §2, p. 6: `Lγ(w) = F(u, v) + ⟨p, Θ(u) + Bv⟩ + (γ/2)‖Θ(u) + Bv‖²` and the stationarity
display "0 ∈ ∂Lγ(w) = (∇uG(u, v) + ∂J(u) + NU(u) + (∇Θ(u))⊤[p + γ(Θ(u) + Bv)], …)", whose
normal cone block `NU(u) = ∂IU(u)` (Definition 2.1(iv)) shows that `∂Lγ` is the subdifferential of
`Lγ` together with the indicator of `U`.

`Ltil P γ w = L_γ(u, v, p)` if `u ∈ U`, and `+∞` otherwise.

**Formalization Note.** paper.md Reading 1: every `∂Lγ` of the paper (Proposition 3.1,
Theorem 4.1(iv), Definition 6.1 applied in Proposition 6.1) is `limSubdiff (Ltil P γ)`. At the
iterates `w^{k+1}` (`u^{k+1} ∈ U`) and at their accumulation points (`U` closed), `Ltil` equals
`L_γ`. -/
noncomputable def Ltil {n d m : ℕ} (P : Problem n d m) (γ : ℝ) (w : W n d m) : EReal := by
  classical
  exact if w.fst.fst ∈ P.U then augLag P γ w.fst.fst w.fst.snd w.snd else ⊤

end NAPPAL.VPEB


