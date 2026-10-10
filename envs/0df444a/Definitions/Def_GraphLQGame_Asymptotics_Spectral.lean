-- Prove2me | Definitions.Def_GraphLQGame_Asymptotics_Spectral
-- name    : GraphLQGame_Asymptotics_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:26.936801+00:00
-- url     : https://prove2.me/theorems/65084f2c-4b7e-41b1-8145-f1dc9f2f8cf7
-- title:
--   Spectral objects: $\mu_G$ (2.8), $\mathcal P_{\mathrm{Lap}}$, $Q_\mu$ (3.1), the ODE on $\mathbb R_+$, $V_\mu$ (2.11) and weak convergence
-- statement:
--   1. The **empirical eigenvalue distribution** of a graph $G$ on $n$ vertices is
--   $$\mu_G := \frac1n\sum_{i=1}^n \delta_{\lambda^G_i},$$
--   where $\lambda^G_1,\dots,\lambda^G_n$ are the eigenvalues of $L_G$, repeated by multiplicity (2.8).
--   2. $\mathcal P_{\mathrm{Lap}}$ is the set of probability measures on $[-2,0]$ with mean $-1$.
--   3. For a measure $\mu$, $Q_\mu(x) := \exp\int_{[-2,0]}\log(1 - x\lambda)\,\mu(d\lambda)$ (3.1). For $\mu = \mu_G$ this is $Q_G$.
--   4. A function $f:\mathbb R_+\to\mathbb R_+$ solves the ODE of Proposition 3.2 for $Q$ if it is continuous on $\mathbb R_+$, continuously differentiable on $(0,\infty)$, $f(0) = 0$ and $f'(t) = c\,Q'(f(t))$ for every $t>0$.
--   5. For a function $f$ (in the paper, $f = f_\mu$),
--   $$V_\mu(t) := \sigma^2\int_0^t\int_{[-2,0]}\Big(\frac{1 - \lambda f(T-t)}{1-\lambda f(T-s)}\Big)^2\mu(d\lambda)\,ds\qquad (2.11),\ (3.6).$$
--   6. A sequence of measures $\mu_k$ on $\mathbb R$ **converges weakly** to $\mu$ if $\int h\,d\mu_k\to\int h\,d\mu$ for every bounded continuous $h:\mathbb R\to\mathbb R$.
--
--   These objects carry the large-graph limit: Theorem 2.6 states the limit of the equilibrium in terms of $Q_\mu$, $f_\mu$ and $V_\mu$ for the weak limit $\mu$ of $\mu_{G_n}$.
--
--   **Formalization Note** The eigenvalues of $L_G$ are the real roots (with multiplicity) of its characteristic polynomial. For a transitive $G$ without isolated vertices $L_G$ is symmetric with all $n$ eigenvalues in $[-2,0]$, so $\mu_G$ is then a probability measure; the definition does not assume this. $V_\mu$ takes $c$ as an (unused) argument to keep the signature shared with the rest of the series. $\mathcal P_{\mathrm{Lap}}$-convergence in the paper uses test functions continuous on $[-2,0]$, which is the same thing for measures carried by $[-2,0]$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), (2.8) p. 7, Theorem 2.6 and (2.11) p. 8, §3 (3.1) p. 19, Proposition 3.2 p. 20, (3.6) p. 21

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Spectral

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction Topology

namespace GraphLQGame.Asymptotics

/-- The limiting variance
`V_μ(t) = σ² ∫₀ᵗ ∫_{[−2,0]} ((1 − λ f(T − t)) / (1 − λ f(T − s)))² μ(dλ) ds`
((2.11), p. 8; (3.6), p. 21), for a given function `f` (in the paper `f = f_μ`). -/
noncomputable def Vmu (σ c T : ℝ) (μ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  σ ^ 2 * ∫ s in (0 : ℝ)..t,
    ∫ l in Set.Icc (-2 : ℝ) 0, ((1 - l * f (T - t)) / (1 - l * f (T - s))) ^ 2 ∂μ

/-- Weak convergence of a sequence of measures on `ℝ` (p. 8, p. 19): `∫ h dμ_k → ∫ h dμ` for every
bounded continuous `h : ℝ → ℝ`. -/
def WeakTendsto (μs : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ h : ℝ →ᵇ ℝ, Filter.Tendsto (fun k => ∫ x, h x ∂(μs k)) Filter.atTop (𝓝 (∫ x, h x ∂μ))

end GraphLQGame.Asymptotics


