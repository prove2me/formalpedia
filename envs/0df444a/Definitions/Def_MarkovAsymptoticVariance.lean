-- Prove2me | Definitions.Def_MarkovAsymptoticVariance
-- name    : MarkovAsymptoticVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T15:59:40.67351+00:00
-- url     : https://prove2.me/theorems/e8905bec-1928-4c19-a246-cd344c5669e1
-- title:
--   Lagged autocovariances and the asymptotic variance of a Markov chain
-- statement:
--   For a Markov kernel $P$ with stationary distribution $\pi$, the lag-$k$ autocovariance of the stationary chain between functionals $f$ (at time $0$) and $g$ (at time $k$) is $$\mathrm{Cov}_\pi(f(X_0), g(X_k)) = \int (f(x) - E_\pi f)\,\bigl(P^k g(x) - E_\pi g\bigr)\, d\pi(x),$$ where $P^k g(x) = \int g\, dP^k(x,\cdot)$. The **asymptotic covariance** of the sample averages of $f$ and $g$ is $$\Sigma(f,g) = \mathrm{Cov}_\pi(f,g) + \sum_{k\ge 1} \mathrm{Cov}_\pi(f(X_0), g(X_k)) + \sum_{k\ge 1} \mathrm{Cov}_\pi(g(X_0), f(X_k)),$$ and the **asymptotic variance** is $\sigma^2(f) = \Sigma(f,f) = \mathrm{Var}_\pi(f) + 2\sum_{k\ge 1}\mathrm{Cov}_\pi(f(X_0), f(X_k))$ — the variance appearing in the Markov chain central limit theorem (the `tsum`s are $0$ by convention when the series diverge).
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, Appendix EC.3, Lemma EC.4 (asymptotic covariance; citing Vats 2017); see also Jones 2004, On the Markov Chain Central Limit Theorem, eq. (1)

import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
The lagged autocovariances of a stationary Markov chain and the asymptotic
variance/covariance appearing in the Markov chain central limit theorem:
`σ²(f) = Var_π(f(X₀)) + 2 ∑_{k≥1} Cov_π(f(X₀), f(X_k))`.

Source: Chen, Simchi-Levi, Wang, *Improving the Estimation of Lifetime Effects
in A/B Testing via Treatment Locality* (arXiv:2407.19618), Appendix EC.3,
Lemma EC.4 (multivariate Markov chain CLT, citing Vats 2017): the asymptotic
covariance `Σ_f = Var[f(X₁)] + ∑_{i≥1} Cov[f(X₁), f(X_{1+i})]
+ ∑_{i≥1} Cov[f(X_{1+i}), f(X₁)]`.  See also Jones, *On the Markov Chain
Central Limit Theorem*, Probability Surveys 1 (2004), eq. (1) and §3.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovChainCLT

/-- The lag-`k` autocovariance of the stationary chain with kernel `P` and
stationary distribution `π`, between functionals `f` (at time `0`) and `g`
(at time `k`): `Cov_π(f(X₀), g(X_k)) = ∫ (f(x) - E_π f) (P^k g (x) - E_π g) dπ(x)`,
where `P^k g (x) = ∫ g dP^k(x, ·)` is the `k`-step conditional expectation.
At `k = 0` this is the ordinary covariance `Cov_π(f, g)`. -/
noncomputable def lagCovariance {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    (π : Measure X) (f g : X → ℝ) (k : ℕ) : ℝ :=
  ∫ x, (f x - ∫ y, f y ∂π) * ((∫ y, g y ∂(iterKernel P k x)) - ∫ y, g y ∂π) ∂π

/-- The asymptotic covariance of the sample averages of `f` and `g` along the
stationary chain: `Cov_π(f, g) + ∑_{k≥1} Cov_π(f(X₀), g(X_k))
+ ∑_{k≥1} Cov_π(g(X₀), f(X_k))` (Lemma EC.4 of arXiv:2407.19618; the `tsum`s
are `0` by convention if the series fail to converge). -/
noncomputable def asymptoticCovariance {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) (π : Measure X) (f g : X → ℝ) : ℝ :=
  lagCovariance P π f g 0 + (∑' k : ℕ, lagCovariance P π f g (k + 1))
    + (∑' k : ℕ, lagCovariance P π g f (k + 1))

/-- The asymptotic variance `σ²(f) = Var_π(f) + 2 ∑_{k≥1} Cov_π(f(X₀), f(X_k))`
of the sample average of `f` along the stationary chain — the variance appearing
in the Markov chain central limit theorem. -/
noncomputable def asymptoticVariance {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) (π : Measure X) (f : X → ℝ) : ℝ :=
  asymptoticCovariance P π f f

end MarkovChainCLT


