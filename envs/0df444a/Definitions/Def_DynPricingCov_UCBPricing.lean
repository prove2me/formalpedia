-- Prove2me | Definitions.Def_DynPricingCov_UCBPricing
-- name    : DynPricingCov_UCBPricing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:40.904728+00:00
-- url     : https://prove2.me/theorems/4c56692d-4922-49e7-bc35-b6f55b7d8b7b
-- title:
--   Regularized quasi-likelihood estimator (3) and Algorithm 1 (UCB Pricing)
-- statement:
--   Within the generalized linear demand model, the **regularized quasi-likelihood estimator** with parameter $\lambda>0$ is
--
--   $$
--   \hat\theta_t\in\arg\max_{\theta\in\Theta}\ -\frac{\lambda\underline g\|\theta\|_2^2}{2}+\sum_{t'=1}^t l_{t'}(\theta),\qquad (3)
--   $$
--
--   where $l_t(\theta)=-\int_{D_t}^{g(z_t^\top\theta)}\frac{u-D_t}{h(u)}\,du$ with $h(u)=g'(g^{-1}(u))$ is the quasi-likelihood (2). Here it is used in the integrated form $\ell_t(\theta)=D_t\,z_t^\top\theta-\int_0^{z_t^\top\theta}g(s)\,ds$, which differs from $l_t$ by a term free of $\theta$.
--
--   **Algorithm 1 (UCB Pricing)** with parameter $\lambda$ runs, for $t=1,\dots,T$:
--
--   1. compute $\hat\theta_{t-1}$ by (3) and the confidence set
--   $$
--   \Theta_t=\Big\{\theta\in\Theta:\ \|\theta-\hat\theta_{t-1}\|_{M_{t-1}}\le2\sqrt\lambda\,\bar\theta+\frac{2\bar\sigma}{\underline g}\sqrt{2\log T+2d\log\frac{2d\lambda+T}{2d\lambda}}\Big\};
--   $$
--   2. observe $x_t$ and choose $(\alpha_t,\beta_t)\in\arg\max_{(\alpha,\beta)\in\Theta_t}r^*(x_t^\top\alpha,x_t^\top\beta)$;
--   3. set $p_t\in\arg\max_{p\in[\underline p,\bar p]}r(p;x_t^\top\alpha_t,x_t^\top\beta_t)$.
--
--   The module also defines the confidence volume $\bar\gamma=2\bar\theta+\frac{2\bar\sigma}{\underline g}\sqrt{2\log T+2d\log\frac{2d+T}{2d}}$, the radius at $\lambda=1$.
--
--   **Formalization Note** The estimator and the run are predicates on processes: any maximizers are allowed, and the demands inside (3) are the run's own. The integrated form $\ell_t$ is defined for every demand, while (2) needs $g^{-1}(D_t)$. At $t=0$ the sum in (3) is empty, so $\hat\theta_0=0$; $M_0=\lambda I_{2d}$. Non-anticipation of the prices is a separate hypothesis of the theorems.
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, §3.1, (2), (3), p.5; Algorithm 1, (4), p.7; Theorem 1 (γ̄), p.7

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_DynPricingCov_Model

open MeasureTheory Matrix

namespace DynPricingCov

/-- The quasi-likelihood of one observation, in integrated form:
`ℓ(θ) = D · zᵀθ − ∫₀^{zᵀθ} g(s) ds`, for the paper's
`l_t(θ) = −∫_{D_t}^{g(z_tᵀθ)} (u − D_t)/h(u) du`, `h(u) = g′(g⁻¹(u))`, arXiv:2112.13254v3,
(2), p.5.

**Formalization Note** Substituting `u = g(s)` in (2) gives `ℓ` plus a term that depends on `D_t`
only, so the objective (3) has the same maximizers. Unlike (2), `ℓ` needs no `g⁻¹(D_t)` and is
defined for every demand. Its gradient is `ξ_t(θ) z_t`, as in (20), p.25. -/
noncomputable def qlik {d : ℕ} (g : ℝ → ℝ) (D : ℝ) (zt θ : Fin (d + d) → ℝ) : ℝ :=
  D * (zt ⬝ᵥ θ) - ∫ s in (0 : ℝ)..(zt ⬝ᵥ θ), g s

/-- The objective of the regularized quasi-likelihood estimator (3), arXiv:2112.13254v3, p.5:
`−λ g̲ ‖θ‖₂²/2 + Σ_{t′=1}^t ℓ_{t′}(θ)`, built from the run's own demands `D_{t′}` and regressors
`z_{t′}`. -/
noncomputable def qmleObjective {Ω : Type} {d : ℕ} (g : ℝ → ℝ) (glo lam : ℝ)
    (θstar : Fin (d + d) → ℝ) (x : ℕ → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ)
    (θ : Fin (d + d) → ℝ) (ω : Ω) : ℝ :=
  -(lam * glo * (θ ⬝ᵥ θ)) / 2 +
    ∑ t' ∈ Finset.Icc 1 t, qlik g (demand g θstar x ε p t' ω) (zProc x p t' ω) θ

/-- `θh` is a regularized quasi-maximum-likelihood estimate at time `t`, i.e. a maximizer over `Θ`
of the objective (3), arXiv:2112.13254v3, p.5:
`θ̂_t ∈ argmax_{θ ∈ Θ} −λ g̲ ‖θ‖₂²/2 + Σ_{t′=1}^t l_{t′}(θ)`.

**Formalization Note** The estimator is a maximality predicate, so every maximizer (every
tie-breaking rule) is allowed. At `t = 0` the sum is empty and `θ̂_0 = 0`. -/
def IsQMLE {Ω : Type} {d : ℕ} (g : ℝ → ℝ) (glo lam θbar : ℝ) (θstar : Fin (d + d) → ℝ)
    (x : ℕ → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (θh : Fin (d + d) → ℝ) : Prop :=
  θh ∈ Theta d θbar ∧
    ∀ θ ∈ Theta d θbar, qmleObjective g glo lam θstar x ε p t θ ω ≤
      qmleObjective g glo lam θstar x ε p t θh ω

/-- The confidence radius of Algorithm 1 and Corollary 1, arXiv:2112.13254v3, pp.6–7:
`2√λ θ̄ + (2σ̄/g̲) √(2 log T + 2d log((2dλ + T)/(2dλ)))`. -/
noncomputable def radius (d T : ℕ) (θbar σbar glo lam : ℝ) : ℝ :=
  2 * Real.sqrt lam * θbar + 2 * σbar / glo *
    Real.sqrt (2 * Real.log T + 2 * d * Real.log ((2 * d * lam + T) / (2 * d * lam)))

/-- The confidence volume `γ̄ = 2θ̄ + (2σ̄/g̲) √(2 log T + 2d log((2d + T)/(2d)))`,
arXiv:2112.13254v3, Theorem 1, p.7 (and Appendix C, p.25). It is the radius with `λ = 1`. -/
noncomputable def gammaBar (d T : ℕ) (θbar σbar glo : ℝ) : ℝ :=
  2 * θbar + 2 * σbar / glo *
    Real.sqrt (2 * Real.log T + 2 * d * Real.log ((2 * d + T) / (2 * d)))

/-- The confidence set `{θ ∈ Θ : ‖θ − θ̂‖_M ≤ ρ}`; with `θ̂ = θ̂_{t−1}`, `M = M_{t−1}` and the radius
of Algorithm 1 it is the set `Θ_t` of Algorithm 1, arXiv:2112.13254v3, p.7. -/
def confSet (d : ℕ) (θbar : ℝ) (θh : Fin (d + d) → ℝ) (M : Matrix (Fin (d + d)) (Fin (d + d)) ℝ)
    (ρ : ℝ) : Set (Fin (d + d) → ℝ) :=
  {θ | θ ∈ Theta d θbar ∧ mNorm M (θ - θh) ≤ ρ}

/-- **Algorithm 1 (UCB Pricing)**, arXiv:2112.13254v3, p.7, with regularization parameter `λ`:
`(θhat, θalg, p)` is a run on periods `t = 1, …, T` when, at every `t` and every outcome `ω`,
1. `θhat (t − 1)` is the estimator `θ̂_{t−1}` of (3) (computed from the run's own data);
2. `θalg t = (α_t, β_t)` lies in `Θ_t = {θ ∈ Θ : ‖θ − θ̂_{t−1}‖_{M_{t−1}} ≤ 2√λ θ̄ + (2σ̄/g̲)
   √(2 log T + 2d log((2dλ + T)/(2dλ)))}`;
3. `θalg t` maximizes `r*(x_tᵀα, x_tᵀβ)` over `(α, β) ∈ Θ_t` (4);
4. `p t ∈ [p̲, p̄]` maximizes `r(p; x_tᵀα_t, x_tᵀβ_t)` over `[p̲, p̄]`.

**Formalization Note** Every "arg max" is a maximality predicate: any maximizers are allowed. The
run is a relation on processes; non-anticipation of the prices is a separate hypothesis. -/
def IsUCBRun {Ω : Type} (d T : ℕ) (x : ℕ → Fin d → ℝ) (g : ℝ → ℝ)
    (θbar plo phi glo σbar : ℝ) (θstar : Fin (d + d) → ℝ) (ε : ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ)
    (lam : ℝ) (θhat θalg : ℕ → Ω → Fin (d + d) → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ ω : Ω,
    IsQMLE g glo lam θbar θstar x ε p (t - 1) ω (θhat (t - 1) ω) ∧
    θalg t ω ∈ confSet d θbar (θhat (t - 1) ω) (designM lam x p (t - 1) ω)
      (radius d T θbar σbar glo lam) ∧
    (∀ θ ∈ confSet d θbar (θhat (t - 1) ω) (designM lam x p (t - 1) ω)
        (radius d T θbar σbar glo lam),
      rstar g plo phi (x t ⬝ᵥ alphaOf θ) (x t ⬝ᵥ betaOf θ) ≤
        rstar g plo phi (x t ⬝ᵥ alphaOf (θalg t ω)) (x t ⬝ᵥ betaOf (θalg t ω))) ∧
    p t ω ∈ Set.Icc plo phi ∧
    ∀ q ∈ Set.Icc plo phi,
      r g q (x t ⬝ᵥ alphaOf (θalg t ω)) (x t ⬝ᵥ betaOf (θalg t ω)) ≤
        r g (p t ω) (x t ⬝ᵥ alphaOf (θalg t ω)) (x t ⬝ᵥ betaOf (θalg t ω))

end DynPricingCov


