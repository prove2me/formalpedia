-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:23:31.850874+00:00
-- url     : https://prove2.me/theorems/ece39163-0720-4870-a4c8-fe5c8887a056
-- title:
--   A sequential sufficient statistic
-- statement:
--   **A sequential sufficient statistic** of a Bayesian Model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.3, pp.160–161, PDF 173–174, and Definition 5.4.5, p.162, PDF 175): an arbitrary measurable space $I$ of information states, measurable maps $t_n : \tilde{H}_n \to  I$ and a transition kernel $\hat{\mu}$ from $I$ to $\Theta $ with $\mu _n(C|\tilde{h}_n) = \hat{\mu}(C|t_n(\tilde{h}_n))$ for all $\tilde{h}_n$, $C$, $n$, and a measurable $\hat{\Phi} : E_X \times  I \times  A \times  \mathcal Z  \to  I$ with $t_{n+1}(\tilde{h}_n, a_n, z_{n+1}, x_{n+1}) = \hat{\Phi}(x_n, t_n(\tilde{h}_n), a_n, z_{n+1})$.
--
--   **Formalization Note.** The identity with the posterior is required wherever the posterior is defined by (5.7) (`BayesModel.posterior = some _`). $\hat{\mu}$ is a Markov kernel (a stochastic transition kernel), so $\hat{\mu}(\cdot |i)$ is a probability measure.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 5.4.3, pp.160–161, PDF 173–174, and Definition 5.4.5, p.162, PDF 175

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **A sequential sufficient statistic** of a Bayesian Model (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), Definition 5.4.3, pp.160–161, PDF 173–174, and
Definition 5.4.5, p.162, PDF 175): an arbitrary measurable space `I` of information states,
measurable maps `t_n : H̃_n → I` and a transition kernel `μ̂` from `I` to `Θ` with
`μ_n(C|h̃_n) = μ̂(C|t_n(h̃_n))` for all `h̃_n`, `C`, `n`, and a measurable `Φ̂ : E_X × I × A × 𝒵 → I` with
`t_{n+1}(h̃_n, a_n, z_{n+1}, x_{n+1}) = Φ̂(x_n, t_n(h̃_n), a_n, z_{n+1})`.

**Formalization Note.** The identity with the posterior is required wherever the posterior is
defined by (5.7) (`BayesModel.posterior = some _`). `μ̂` is a Markov kernel (a stochastic transition
kernel), so `μ̂(·|i)` is a probability measure. -/
structure SeqSuffStat {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ) (I : Type*)
    [MeasurableSpace I] where
  /-- The statistics `t_n : H̃_n → I`. -/
  t : (n : ℕ) → Htil EX A Z n → I
  t_meas : ∀ n, Measurable (t n)
  /-- The kernel `μ̂(·|i)`. -/
  muhat : Kernel I Θ
  muhat_markov : IsMarkovKernel muhat
  suff : ∀ n h ρ, M.posterior n h = some ρ → ρ = muhat (t n h)
  /-- The update `Φ̂`. -/
  Phihat : EX × I × A × Z → I
  Phihat_meas : Measurable Phihat
  seq : ∀ n (h : Htil EX A Z n) a z x', t (n + 1) (h, a, z, x') = Phihat (Htil.state n h, t n h, a, z)

attribute [instance] SeqSuffStat.muhat_markov

end BauerleRiederMDP.LQ.Supplement


