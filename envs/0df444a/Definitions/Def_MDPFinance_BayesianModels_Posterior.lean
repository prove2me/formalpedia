-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_Posterior
-- name    : MDPFinance_BayesianModels_Posterior
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:20:03.23236+00:00
-- url     : https://prove2.me/theorems/5afda9ab-3103-47d7-bd94-db9db6f71202
-- title:
--   The posterior/filter process $(\mu_n)$
-- statement:
--   This definition packages the **posterior (filter) process** $(\mu_n)$ of a Bayesian Model:
--   for every stage $n$ and observable history $\tilde h_n = (xs,as,zs)$, $\mu_n(\cdot\mid\tilde h_n)$
--   is the conditional distribution of the unknown parameter $\theta$ given everything observed so
--   far, $\mu_n(C\mid\tilde h_n) := \mathbb P_x^\pi(\theta \in C \mid X_0,A_0,Z_1,\dots,X_n)$.
--
--   Rather than constructing this conditional law from a canonical probability space (general
--   conditioning theory that the book itself invokes but does not reprove), `Posterior` bundles it as
--   data satisfying its two defining properties: it agrees with the prior at $n=0$ (`hmu0`), and it
--   updates by the one-step Bayes rule
--   $$
--   \mu_{n+1}(C \mid \tilde h_n, a_n, z_{n+1}) =
--   \frac{\int_C q_Z(x_n,\theta,a_n,z_{n+1})\,\mathrm d\mu_n(\tilde h_n)(\theta)}
--        {\int_\Theta q_Z(x_n,\theta,a_n,z_{n+1})\,\mathrm d\mu_n(\tilde h_n)(\theta)}
--   $$
--   (`hmu_rec`), together with non-anticipation in the history (`hmu_dep`) and being a probability
--   measure at every stage (`hmu_prob`).
--
--   This is exactly Bäuerle and Rieder's own Bayes operator $\Phi$ (Example 5.2.4, Eq. (5.7))
--   iterated once per stage; Lemma 5.4.1's closed-form, $n$-fold-product formula for $\mu_n$ is then
--   a genuine theorem (by induction), not built into this definition.
--
--   **Formalization Note.** Matches the "data satisfying a defining formula" pattern of
--   `MDPFinance.POMDP.FilterData.Phi`/`hPhi` (chunk `05a`).
--
--   **Moderation note.** Two changes. (1) `hmu_meas`: $\tilde h_n\mapsto\mu_n(C\mid\tilde h_n)$ is measurable, as a conditional distribution (stochastic kernel) is; without it the integral in Lemma 5.4.2 is a default value. (2) The Bayes update `hmu_rec` is stated with Lebesgue integrals and required only where the normalizing constant $\int q_Z(x_n,\theta,a_n,z_{n+1})\mu_n(d\theta)$ is positive and finite. The draft demanded the quotient at every $z_{n+1}$; at an observation of zero likelihood (e.g. $z\le 0$ for the exponential model of Example 5.4.4(i) on $Z=\mathbb R$) it demanded $\mu_{n+1}(\Theta)=0/0=0$, which no probability measure satisfies, so no `Posterior` existed and every theorem using one was vacuous. Such observations form a null set for the predictive law of $Z_{n+1}$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 159-160, p. 159-160 (unnumbered, underlies Lemma 5.4.1)

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- The **posterior/filter process** `(μ_n)` of a Bayesian Model (Bäuerle–Rieder, p. 159-160,
PDF 172-173, `μ_n(C|h̃_n) := ℙ^π_x(θ ∈ C \mid X_0,A_0,Z_1,\dots,X_n)`): a family of probability
measures on `Θ`, one for every stage `n` and observable history `h̃_n = (xs,as,zs)`, non-
anticipating in the history, agreeing with the prior at `n = 0`, and satisfying the one-step
Bayes update `μ_{n+1}(C|h̃_n,a_n,z_{n+1}) = [∫_C q_Z(x_n,θ,a_n,z_{n+1}) dμ_n(h̃_n)(θ)] /
[∫_Θ q_Z(x_n,θ,a_n,z_{n+1}) dμ_n(h̃_n)(θ)]` (Bäuerle–Rieder, Example 5.2.4, Eq. (5.7), p. 155,
PDF 168, the Bayes operator `Φ` specialized to the Bayesian Model). Existence of `μ_n` as a
genuine regular conditional probability is the book's own standing assumption (general
conditioning theory, not reproved here); it is *data*, characterized by its defining properties,
exactly as `MDPFinance.POMDP.FilterData.Phi`/`hPhi` (chunk `05a`) bundles the general Bayes
operator. Lemma 5.4.1's explicit `n`-fold product formula is then a genuine consequence of
`hmu0`/`hmu_rec` by induction (see `Thm_MDPFinance_BayesianModels_lemma_5_4_1.lean`), not built
into this definition. -/
structure BayesModel.Posterior (M : BayesModel EX Θ A Z) where
  mu : (n : ℕ) → (ℕ → EX) → (ℕ → A) → (ℕ → Z) → Measure Θ
  hmu_prob : ∀ n xs as zs, IsProbabilityMeasure (mu n xs as zs)
  hmu_dep : ∀ n xs xs' as as' zs zs', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) →
    (∀ i, 1 ≤ i → i ≤ n → zs i = zs' i) → mu n xs as zs = mu n xs' as' zs'
  hmu0 : ∀ xs as zs, mu 0 xs as zs = M.Q0
  /-- `h̃_n ↦ μ_n(C|h̃_n)` is measurable (`μ_n` is a stochastic kernel from `H̃_n` to `Θ`). -/
  hmu_meas : ∀ n (C : Set Θ), MeasurableSet C →
    Measurable fun p : (ℕ → EX) × (ℕ → A) × (ℕ → Z) => mu n p.1 p.2.1 p.2.2 C
  /-- The one-step Bayes update (5.7), required wherever it defines a probability measure, i.e.
  wherever the normalizing constant `∫ q_Z(x_n,θ,a_n,z_{n+1}) μ_n(dθ)` is positive and finite
  (elsewhere the book's quotient is `0/0` or `∞/∞`; such `z_{n+1}` form a null set for the
  predictive law of `Z_{n+1}`). -/
  hmu_rec : ∀ n xs as zs,
    0 < (∫⁻ θ, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs)) →
    (∫⁻ θ, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs)) < ⊤ →
    ∀ (C : Set Θ), MeasurableSet C →
    mu (n + 1) xs as zs C =
      (∫⁻ θ in C, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs)) /
        (∫⁻ θ, ENNReal.ofReal (M.qZ (xs n) θ (as n) (zs (n + 1))) ∂(mu n xs as zs))

end MDPFinance.BayesianModels


