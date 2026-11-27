-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_phiApprox
-- name    : RockafellianRelax_Supplement_phiApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:13:50.171358+00:00
-- url     : https://prove2.me/theorems/672db158-51ce-40a0-a278-ee4aa3ec1685
-- title:
--   $\Phi$-divergence approximating function (4.7)
-- statement:
--   With $f_0,\dots,f_s : \mathbb R^n \to \overline{\mathbb R}$, $\Phi : \mathbb R \to \overline{\mathbb R}$, $p^\nu \in \mathbb R^s$, $\theta^\nu \in \mathbb R$ and the probability simplex $\Delta$, the **approximating function** (4.7) is
--
--   $$
--   f^\nu(u,x) = \begin{cases} f_0(x) + \sum_{i=1}^s (p^\nu_i+u_i) f_i(x) + \theta^\nu d_\Phi(p^\nu+u\,|\,p^\nu), & p^\nu+u\in\Delta,\\ +\infty, & \text{otherwise.}\end{cases}
--   $$
--
--   Theorem 4.4 shows that these functions epi-converge to the Rockafellian (4.2).
--
--   **Formalization Note** The indicator is written by cases, and $0\cdot\infty = 0$ covers $\theta^\nu = 0$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, display (4.7), p.15

import Mathlib
import Definitions.Def_RockafellianRelax_Supplement_expObjective
import Definitions.Def_RockafellianRelax_Supplement_phiDivergence

namespace RockafellianRelax.Supplement

open Classical in
/-- **Approximating function (4.7).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, (4.7), p.15: "fν(u, x) = f₀(x) + ∑_{i=1}^s (pν_i + u_i)
f_i(x) + θν d_Φ(pν + u|pν) + ι_∆(pν + u)".

**Formalization Note.** `q` stands for `pν` and `θ` for `θν`. The perturbed vector is the first
argument of the divergence and `q` the second. The function is the formula on
`q + u ∈ ∆ = stdSimplex ℝ (Fin s)` and `⊤` elsewhere. `0 * ⊤ = 0` covers `θ = 0`. -/
noncomputable def phiApprox {n s : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (fi : Fin s → (Fin n → ℝ) → EReal) (Φ : ℝ → EReal) (q : Fin s → ℝ) (θ : ℝ) :
    (Fin s → ℝ) × (Fin n → ℝ) → EReal :=
  fun z =>
    if q + z.1 ∈ stdSimplex ℝ (Fin s) then
      expObjective f0 fi (q + z.1) z.2 + (θ : EReal) * phiDivergence Φ (q + z.1) q
    else ⊤

end RockafellianRelax.Supplement


