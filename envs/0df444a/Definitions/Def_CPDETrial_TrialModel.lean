-- Prove2me | Definitions.Def_CPDETrial_TrialModel
-- name    : CPDETrial_TrialModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:52:23.628191+00:00
-- url     : https://prove2.me/theorems/a722bfd6-a56a-4e6e-8b85-fcf09c888c49
-- title:
--   The Bayesian trial model
-- statement:
--   On a probability space $(\Omega,\mathbb P)$:
--
--   1. $\theta$ is a random vector with law $N(\mu^0,\Sigma^0)$;
--   2. each sampling error $\varepsilon^t_i$ has law $N(0,\lambda_i)$;
--   3. the errors $(\varepsilon^t_i)_{t,i}$ are mutually independent and independent of $\theta$;
--   4. $\mathcal G$ is a sub-$\sigma$-algebra (external randomization) independent of $\theta$ and the errors.
--
--   Observations are $Y^t_i=\theta_i+\varepsilon^t_i$, so that $Y^t_i\mid\theta\sim N(\theta_i,\lambda_i)$ independently, as in §1.2 of the paper.
--
--   **Formalization Note** Mathlib's multivariate Gaussian with a covariance that is not positive semidefinite is a point mass; every theorem assumes $\Sigma^0$ positive definite.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 6, §1.2

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The Bayesian trial model of §1.2.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.2, p. 6: "We assume that observations are independent and normally distributed,
conditional on the unknown mean, so that `Y^t_i | θ_i ∼ N(θ_i, λ_i)` for `t = 1, 2, …` and
`i ∈ M`"; "`θ ∼ N(µ⁰, Σ⁰)`".

`TrialModel P mu0 Sig0 lam θ ε 𝓖` says, on the probability space `(Ω, P)`:
1. `θ` is measurable with law `N(µ⁰, Σ⁰)` (Mathlib's `multivariateGaussian`);
2. every sampling error `ε t i` is measurable with law `N(0, λ_i)`;
3. the family `(ε t i)_{(t,i)}` is mutually independent, and independent of `θ`;
4. `𝓖` is a sub-`σ`-algebra (the external randomization) independent of `(θ, (ε t i)_{t,i})`.
The observations are `Y^t_i = θ_i + ε t i` (see `obs`).

**Formalization Note.** `µ⁰ : Fin M → ℝ` is converted to `EuclideanSpace ℝ (Fin M)` by
`WithLp.toLp 2`. Mathlib's `multivariateGaussian µ S` is the Dirac mass at `µ` when `S` is not
positive semidefinite; every theorem assumes `Σ⁰` positive definite, so this never applies.
Measurability of `θ` and `ε` is the standing convention for random variables. The ambient
`σ`-algebra `mΩ` is named explicitly, and is an implicit argument read off `P`, because `𝓖` is a
second `MeasurableSpace Ω` in scope. -/
def TrialModel {M : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (mu0 : Fin M → ℝ) (Sig0 : Matrix (Fin M) (Fin M) ℝ) (lam : Fin M → ℝ≥0)
    (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ) (𝓖 : MeasurableSpace Ω) : Prop :=
  Measurable[mΩ] θ ∧ @Measure.map Ω _ mΩ _ θ P = multivariateGaussian (WithLp.toLp 2 mu0) Sig0 ∧
  (∀ t i, Measurable[mΩ] (ε t i)) ∧ (∀ t i, @Measure.map Ω ℝ mΩ _ (ε t i) P = gaussianReal 0 (lam i)) ∧
  iIndepFun (fun p : ℕ × Fin M => ε p.1 p.2) P ∧
  Indep (MeasurableSpace.comap θ inferInstance)
    (⨆ p : ℕ × Fin M, MeasurableSpace.comap (ε p.1 p.2) inferInstance) P ∧
  𝓖 ≤ mΩ ∧
  Indep 𝓖 (MeasurableSpace.comap θ inferInstance ⊔
    ⨆ p : ℕ × Fin M, MeasurableSpace.comap (ε p.1 p.2) inferInstance) P

end CPDETrial


