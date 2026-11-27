-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_quadApprox
-- name    : RockafellianRelax_Supplement_quadApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:11:51.156197+00:00
-- url     : https://prove2.me/theorems/cb6c808d-2756-5d47-8b32-a8e583b495d9
-- title:
--   Quadratically penalized approximating function (4.3)
-- statement:
--   Let $f_0,\dots,f_s : \mathbb R^n \to \overline{\mathbb R}$, $p^\nu \in \mathbb R^s$, $\theta^\nu \in \mathbb R$, and let $\Delta$ be the probability simplex. The **approximating function** (4.3) is
--
--   $$
--   f^\nu(u,x) = \begin{cases} f_0(x) + \sum_{i=1}^s (p^\nu_i+u_i) f_i(x) + \tfrac12\theta^\nu\|u\|_2^2, & p^\nu + u \in \Delta,\\ +\infty, & \text{otherwise.}\end{cases}
--   $$
--
--   Problem (4.4) minimizes $f^\nu(u,x) - \langle y^\nu, u\rangle$ jointly in $(u,x)$.
--
--   It is the function whose approximate minimizers Theorem 4.3 analyzes.
--
--   **Formalization Note** The indicator $\iota_\Delta(p^\nu+u)$ is written by cases. On the first branch every coefficient is nonnegative.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, display (4.3) and problem (4.4), p.10

import Mathlib
import Definitions.Def_RockafellianRelax_Supplement_euclidNorm
import Definitions.Def_RockafellianRelax_Supplement_expObjective

namespace RockafellianRelax.Supplement

open Classical in
/-- **Approximating function (4.3).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, (4.3), p.10: "fν(u, x) = f₀(x) + ∑_{i=1}^s (pν_i + u_i)
f_i(x) + ½θν‖u‖₂² + ι_∆(pν + u)". Problem (4.4) minimizes its tilt by `yν`.

**Formalization Note.** `q` stands for `pν` and `θ` for `θν`. The function is defined by cases: the
formula on `q + u ∈ ∆ = stdSimplex ℝ (Fin s)`, where every coefficient is nonnegative, and `⊤`
elsewhere (the paper's value, by `∞ − ∞ = ∞`). -/
noncomputable def quadApprox {n s : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (fi : Fin s → (Fin n → ℝ) → EReal) (q : Fin s → ℝ) (θ : ℝ) :
    (Fin s → ℝ) × (Fin n → ℝ) → EReal :=
  fun z =>
    if q + z.1 ∈ stdSimplex ℝ (Fin s) then
      expObjective f0 fi (q + z.1) z.2 + ((1 / 2 * θ * euclidNorm z.1 ^ 2 : ℝ) : EReal)
    else ⊤

end RockafellianRelax.Supplement


