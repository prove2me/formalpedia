-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping
-- name    : BauerleRiederMDP_LQ_Supplement_BayesStopping
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:59:24.738373+00:00
-- url     : https://prove2.me/theorems/0bcf6554-4115-5489-8b9f-bf65442c33ac
-- title:
--   The data of the Bayesian stopping problem
-- statement:
--   **The data of the Bayesian stopping problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.4, pp.323–324, PDF 331–332, with the information-based model of §5.4, pp.160–163, PDF 173–176): offers $Z_1, Z_2, \dots $ i.i.d. with law $Q(\cdot |\theta )$ given the unknown parameter $\theta  \in  \Theta  \subset  \mathbb R $, where $Q(\cdot |\theta )$ has density $q(z|\theta )$ with respect to a σ-finite measure; observation cost $c$ per offer ($c(x, i) ≡ -c$); a space $I$ of information states with the kernel $\hat{\mu}(d\theta |i)$ (the conditional law of $\vartheta $ given information $i$) and the measurable update $\hat{\Phi}(i, z)$ of the information after observing the offer $z$.
--
--   **Formalization Note.** $\Theta $ is a subset $S\Theta $ of $\mathbb R $ (a subtype). $Qk$ is $Q(\cdot |\theta )$ as a Markov kernel, tied to the density by $Qk_eq$. The book's $\hat{\Phi}$ is the sequential-sufficient-statistic update of §5.4, which is the Bayes rule for $\hat{\mu}$; `bayes` requires this at every information state $i$ for $\hat{Q}^Z(\cdot |i)$-almost every offer $z$ (the posterior is arbitrary on a null set of offers), where $\hat{Q}^Z(\cdot |i) = \int  Q(\cdot |\theta ) \hat{\mu}(d\theta |i)$ is `Qk ∘ₖ muhat`. The prior $Q_0$ enters only through $\hat{\mu}$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.4, pp.323–324, PDF 331–332, with the information-based model of §5.4, pp.160–163, PDF 173–176

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The data of the Bayesian stopping problem** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §10.3.4, pp.323–324, PDF 331–332, with the information-based
model of §5.4, pp.160–163, PDF 173–176): offers `Z_1, Z_2, …` i.i.d. with law `Q(·|θ)` given the
unknown parameter `θ ∈ Θ ⊂ ℝ`, where `Q(·|θ)` has density `q(z|θ)` with respect to a σ-finite
measure; observation cost `c` per offer (`c(x, i) ≡ −c`); a space `I` of information states with
the kernel `μ̂(dθ|i)` (the conditional law of `ϑ` given information `i`) and the measurable update
`Φ̂(i, z)` of the information after observing the offer `z`.

**Formalization Note.** `Θ` is a subset `SΘ` of `ℝ` (a subtype). `Qk` is `Q(·|θ)` as a Markov
kernel, tied to the density by `Qk_eq`. The book's `Φ̂` is the sequential-sufficient-statistic
update of §5.4, which is the Bayes rule for `μ̂`; `bayes` requires this at every information state
`i` for `Q̂^Z(·|i)`-almost every offer `z` (the posterior is arbitrary on a null set of offers),
where `Q̂^Z(·|i) = ∫ Q(·|θ) μ̂(dθ|i)` is `Qk ∘ₖ muhat`. The prior `Q_0` enters only through `μ̂`. -/
structure BayesStopping (SΘ : Set ℝ) (I : Type) [MeasurableSpace I] where
  /-- The observation cost `c` (the one-stage reward is `−c`). -/
  c : ℝ
  /-- The dominating σ-finite measure of the densities. -/
  lam : Measure ℝ
  lam_sigmaFinite : SigmaFinite lam
  /-- The density `q(z|θ)`. -/
  q : ℝ → SΘ → ℝ≥0∞
  q_meas : Measurable (Function.uncurry q)
  /-- The law `Q(·|θ)` of an offer. -/
  Qk : Kernel SΘ ℝ
  Qk_markov : IsMarkovKernel Qk
  Qk_eq : ∀ θ, Qk θ = lam.withDensity fun z => q z θ
  /-- The kernel `μ̂(dθ|i)`. -/
  muhat : Kernel I SΘ
  muhat_markov : IsMarkovKernel muhat
  /-- The information update `Φ̂(i, z)`. -/
  Phihat : I × ℝ → I
  Phihat_meas : Measurable Phihat
  bayes : ∀ i, ∀ᵐ z ∂((Qk ∘ₖ muhat) i),
    muhat (Phihat (i, z)) = (∫⁻ θ, q z θ ∂(muhat i))⁻¹ • (muhat i).withDensity fun θ => q z θ

attribute [instance] BayesStopping.Qk_markov BayesStopping.muhat_markov

end BauerleRiederMDP.LQ.Supplement


