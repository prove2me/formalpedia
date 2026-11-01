-- Prove2me | Definitions.Def_SmoothNestedSim_IsNoiseKernel
-- name    : SmoothNestedSim_IsNoiseKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:19.576989+00:00
-- url     : https://prove2.me/theorems/b0e5f512-95cb-415e-9495-aa5e3dbb4cf2
-- title:
--   Assumption 1: independent zero-mean sub-Gaussian noise, given the design
-- statement:
--   Let $\sigma^2\ge0$. A variable $Z$ is **sub-Gaussian with variance proxy $\sigma^2$**, $Z\sim\mathrm{subG}(\sigma^2)$ (Definition 1), if $\mathbb E[e^{t(Z-\mathbb EZ)}]\le e^{\sigma^2t^2/2}$ for all $t\in\mathbb R$.
--
--   Let $\kappa$ be the conditional law of the noise array $(\epsilon_{ij})_{1\le i\le n,1\le j\le m}$ given the outer-level scenarios $\mathbf x=(\mathbf x_1,\dots,\mathbf x_n)$. **Assumption 1** holds if for every design $\mathbf x$ there are probability laws $\xi_1,\dots,\xi_n$ on $\mathbb R$, each zero-mean $\mathrm{subG}(\sigma^2)$, with
--
--   $$
--   \kappa(\mathbf x) = \bigotimes_{i=1}^n\bigotimes_{j=1}^m \xi_i ,
--   $$
--
--   that is: given the design, the $\epsilon_{ij}$ are independent, zero-mean $\mathrm{subG}(\sigma^2)$, and $\epsilon_{i1},\dots,\epsilon_{im}$ are identically distributed for each $i$. The laws $\xi_i$ may differ across $i$ and depend on the design, so the noise may be heteroscedastic.
--
--   **Formalization Note** The paper states Assumption 1 without mentioning the design; it is read conditionally on $\mathbf x_1,\dots,\mathbf x_n$, as the paper's sampling scheme (§2.1) and proofs require. Zero-mean $\mathrm{subG}(\sigma^2)$ is Mathlib's `HasSubgaussianMGF id σ²`, which forces mean zero.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §4.1, Definition 1 and Assumption 1, p.15; §2.1, p.8

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SmoothNestedSim

/-- **Assumption 1, conditionally on the design** (Wang, Wang, Zhang, *Smooth Nested
Simulation*, arXiv:2201.02958v6, §4.1, p.15): "The noise terms `{ϵᵢⱼ : 1 ≤ i ≤ n, 1 ≤ j ≤ m}`
are independent, zero-mean `subG(σ²)`. Moreover, `ϵᵢ₁, …, ϵᵢₘ` are identically distributed, for
each `i = 1, …, n`." Definition 1, p.15: `Z ∼ subG(σ²)` if `𝔼[e^{t(Z−𝔼Z)}] ≤ e^{σ²t²/2}` for
all `t ∈ ℝ`.

`κ` is the conditional law of the noise array `(ϵᵢⱼ)` given the outer-level scenarios
`x = (x₁, …, xₙ)`. `IsNoiseKernel σ² κ` says: for every design `x` there are probability laws
`ξ₁, …, ξₙ` on `ℝ`, each zero-mean `subG(σ²)`, such that given `x` the `ϵᵢⱼ` are independent
and `ϵᵢⱼ ∼ ξᵢ` for every `j`, i.e. `κ x = ⊗ᵢ ⊗ⱼ ξᵢ`.

**Formalization Note.** Assumption 1 is read conditionally on `x₁, …, xₙ`: the paper generates
the inner samples "from the conditional distribution of `Y` given `X = xᵢ`" (§2.1, p.8), and its
proofs compute variances with the design fixed (EC.4.7, p.ec10). The laws `ξᵢ` may depend on
`i` and on the whole design (heteroscedastic noise, p.15). `subG(σ²)` with mean zero is Mathlib's
`HasSubgaussianMGF id σ²` (`𝔼[e^{tZ}] ≤ e^{σ²t²/2}` for all `t`, with the exponential moments
integrable); it forces mean zero, so zero mean is not a separate clause. The dependence on the
design is measurable because `κ` is a Markov kernel. -/
def IsNoiseKernel {d n m : ℕ} (σsq : ℝ≥0)
    (κ : Kernel (Fin n → EuclideanSpace ℝ (Fin d)) (Fin n → Fin m → ℝ)) : Prop :=
  ∀ x : Fin n → EuclideanSpace ℝ (Fin d), ∃ ξ : Fin n → ProbabilityMeasure ℝ,
    (∀ i, HasSubgaussianMGF id σsq (ξ i : Measure ℝ)) ∧
      κ x = Measure.pi (fun i => Measure.pi (fun _ : Fin m => (ξ i : Measure ℝ)))

end SmoothNestedSim


