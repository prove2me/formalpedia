-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_l1Rockafellian
-- name    : RockafellianRelax_Supplement_l1Rockafellian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:14:46.817823+00:00
-- url     : https://prove2.me/theorems/13994a71-ec82-5008-91c4-d73855efede4
-- title:
--   The $\ell_1$-penalized function of (4.11) and (4.12)
-- statement:
--   For $f_0,\dots,f_s : \mathbb R^n \to \overline{\mathbb R}$, $q \in \mathbb R^s$, $\theta \in \mathbb R$ and the probability simplex $\Delta$, define
--
--   $$
--   (u,x)\mapsto \begin{cases} f_0(x) + \sum_{i=1}^s (q_i+u_i) f_i(x) + \theta\sum_{i=1}^s |u_i|, & q+u\in\Delta,\\ +\infty, & \text{otherwise.}\end{cases}
--   $$
--
--   With $q = p$ it is the Rockafellian (4.11). With $q = p^\nu$ and the same $\theta$ it is the approximating function (4.12).
--
--   **Formalization Note** The indicator is written by cases, and $\|u\|_1 = \sum_i|u_i|$ is written out.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, displays (4.11) and (4.12), p.17

import Mathlib
import Definitions.Def_RockafellianRelax_Supplement_expObjective

namespace RockafellianRelax.Supplement

open Classical in
/-- **The ℓ₁ function of (4.11) and (4.12).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, p.17: "f(u, x) = f₀(x) + ∑_{i=1}^s (p_i + u_i)
f_i(x) + θ‖u‖₁ + ι_∆(p + u)" (4.11), "fν(u, x) = f₀(x) + ∑_{i=1}^s (pν_i + u_i) f_i(x) + θ‖u‖₁ +
ι_∆(pν + u)" (4.12).

**Formalization Note.** (4.11) is this function at `q = p` and (4.12) is it at `q = pν`, with the
same `θ`. `‖u‖₁ = ∑ᵢ |uᵢ|`. The function is the formula on `q + u ∈ ∆ = stdSimplex ℝ (Fin s)` and
`⊤` elsewhere. -/
noncomputable def l1Rockafellian {n s : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (fi : Fin s → (Fin n → ℝ) → EReal) (q : Fin s → ℝ) (θ : ℝ) :
    (Fin s → ℝ) × (Fin n → ℝ) → EReal :=
  fun z =>
    if q + z.1 ∈ stdSimplex ℝ (Fin s) then
      expObjective f0 fi (q + z.1) z.2 + ((θ * ∑ i, |z.1 i| : ℝ) : EReal)
    else ⊤

end RockafellianRelax.Supplement


