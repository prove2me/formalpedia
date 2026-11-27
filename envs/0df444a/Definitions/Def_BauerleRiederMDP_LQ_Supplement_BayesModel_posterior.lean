-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:59:10.344847+00:00
-- url     : https://prove2.me/theorems/fd28d510-7e0d-5542-9760-04fb6fdec593
-- title:
--   The posterior distribution $\mu _n(\cdot |\tilde{h}_n)$
-- statement:
--   **The posterior distribution $\mu _n(\cdot |\tilde{h}_n)$** of the Bayesian Model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.154, PDF 167, filter recursion $\mu _0 := Q_0$, $\mu _{n+1}(\cdot |\tilde{h}_n, a_n, z_{n+1}, x_{n+1}) := \Phi (x_n, \mu _n(\cdot |\tilde{h}_n), a_n, z_{n+1})$, with the Bayes operator (5.7), p.155, PDF 168: $\Phi (x, \rho , a, z)(C) = \int _C q^Z(z|x, \theta , a) \rho (d\theta ) / \int _\Theta  q^Z(z|x, \theta , a) \rho (d\theta )$).
--
--   **Formalization Note.** (5.7) defines $\Phi $ only when the denominator is in $(0, \infty )$. The posterior is `some μ_n` when every denominator along the history is in $(0, \infty )$, and `none` otherwise (histories of zero likelihood, a null set under the predictive law), so no arbitrary version is fixed.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.154, PDF 167, filter recursion `μ_0 := Q_0`, `μ_{n+1}(·|h̃_n, a_n, z_{n+1}, x_{n+1}) := Φ(x_n, μ_n(·|h̃_n), a_n, z_{n+1})`, with the Bayes operator (5.7), p.155, PDF 168: `Φ(x, ρ, a, z)(C) = ∫_C q^Z(z|x, θ, a) ρ(dθ) / ∫_Θ q^Z(z|x, θ, a) ρ(dθ)`

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The posterior distribution `μ_n(·|h̃_n)`** of the Bayesian Model (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), p.154, PDF 167, filter recursion
`μ_0 := Q_0`, `μ_{n+1}(·|h̃_n, a_n, z_{n+1}, x_{n+1}) := Φ(x_n, μ_n(·|h̃_n), a_n, z_{n+1})`, with the Bayes
operator (5.7), p.155, PDF 168:
`Φ(x, ρ, a, z)(C) = ∫_C q^Z(z|x, θ, a) ρ(dθ) / ∫_Θ q^Z(z|x, θ, a) ρ(dθ)`).

**Formalization Note.** (5.7) defines `Φ` only when the denominator is in `(0, ∞)`. The posterior is
`some μ_n` when every denominator along the history is in `(0, ∞)`, and `none` otherwise
(histories of zero likelihood, a null set under the predictive law), so no arbitrary version is
fixed. -/
noncomputable def BayesModel.posterior {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ) :
    (n : ℕ) → Htil EX A Z n → Option (Measure Θ)
  | 0, _ => some M.Q0
  | n + 1, (h, a, z, _) =>
      match BayesModel.posterior M n h with
      | none => none
      | some ρ =>
          if (∫⁻ θ, M.qZ (Htil.state n h, θ, a) z ∂ρ) ≠ 0 ∧
              (∫⁻ θ, M.qZ (Htil.state n h, θ, a) z ∂ρ) ≠ ⊤ then
            some ((∫⁻ θ, M.qZ (Htil.state n h, θ, a) z ∂ρ)⁻¹ •
              ρ.withDensity fun θ => M.qZ (Htil.state n h, θ, a) z)
          else none

end BauerleRiederMDP.LQ.Supplement


