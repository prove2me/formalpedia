-- Prove2me | Definitions.Def_DecDepSO_IsBiasedProxSGDRun
-- name    : DecDepSO_IsBiasedProxSGDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:59.345884+00:00
-- url     : https://prove2.me/theorems/49eff250-3b26-4315-bd48-11470d0932c6
-- title:
--   Algorithm 1 run with the biased oracle of Assumption 7 (c) — $x_{t+1}=\mathrm{prox}_{\eta_t r}(x_t-\eta_t g_t)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$, let $f$, $r$ (with domain $D$), $\bar x$ be as in Assumption 7, and let $B,\sigma\in\mathbb R$. A **run of Algorithm 1 with the biased oracle** consists of step sizes $(\eta_t)_{t\ge0}$, an initial point $x_0\in E$, iterates $x_t:\Omega\to E$ and oracle outputs $g_t:\Omega\to E$ such that, for every $t\ge0$:
--
--   1. $\eta_t>0$, and $x_0$ is the given deterministic starting point;
--   2. $x_t$ is $\mathcal F_t$-measurable, and $g_t$ is $\mathcal F_{t+1}$-measurable with $\mathbb E\|g_t\|^2<\infty$;
--   3. (bias) almost surely $\big\|\mathbb E_t[g_t]-\nabla f(x_t)\big\|\le B\|x_t-\bar x\|$;
--   4. (variance) almost surely $\mathbb E_t\big[\|g_t-\mathbb E_t[g_t]\|^2\big]\le\sigma^2$;
--   5. (step) for every outcome,
--   $$
--   x_{t+1}=\mathrm{prox}_{\eta_t r}(x_t-\eta_t g_t)=\operatorname*{arg\,min}_{y}\Big\{r(y)+\tfrac{1}{2\eta_t}\|y-(x_t-\eta_t g_t)\|^2\Big\}.
--   $$
--
--   Here $\mathbb E_t[\cdot]=\mathbb E[\cdot\mid\mathcal F_t]$. This is Assumption 7 (c) ("for every point $x$, we may draw a realization of a random vector $g(x)$" with $\|\mathbb E[g(x)]-\nabla f(x)\|\le B\|x-\bar x\|$ and $\mathbb E\|g(x)-\mathbb E[g(x)]\|^2\le\sigma^2$) together with Algorithm 1 ("Sample $g_t=g(x_t)$, set $x_{t+1}=\mathrm{prox}_{\eta_t r}(x_t-\eta_t g_t)$"). In the decision-dependent setting of the paper, $g_t=\nabla\ell(x_t,z_t)$ with $z_t\sim\mathcal D(x_t)$ and $B=\gamma\beta$.
--
--   **Formalization Note** A fresh draw $g_t=g(x_t)$, drawn given the past from the oracle's law at $x_t$, satisfies 3 and 4 with $\mathcal F_t=\sigma(g_0,\dots,g_{t-1})$; the paper's $\mathbb E_t$, conditioning on $x_0,\dots,x_t$ only, is recovered by the tower property. Conditional expectations are Mathlib's `condExp`; square integrability of $g_t$ makes them well defined. The prox is the published minimizer predicate `GoldenRatioVI.IsProx` applied to $\eta_t r$ (minimizing $\eta_t r(y)+\frac12\|y-w\|^2$ has the same minimizers); under Assumption 7 the minimizer exists and is unique. The run is infinite; a run of Algorithm 1 up to $T$ is its first $T+1$ steps.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Assumption 7 (c), p.25; Algorithm 1, p.25; definition of E_t, p.26; prox, p.5

import Mathlib
import Definitions.Def_GoldenRatioVI_IsProx

open MeasureTheory

namespace DecDepSO

/-- **A run of Algorithm 1 (stochastic proximal gradient) with the biased oracle of
Assumption 7 (c).**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Assumption 7 (c), p.25: "For every point x, we may draw a realization of a
random vector g(x) ∈ Rd satisfying the bias/variance bounds: ‖E[g(x)] − ∇f(x)‖ ≤ B‖x − x̄‖ and
E‖g(x) − E[g(x)]‖² ≤ σ²"; Algorithm 1, p.25: "Input: initial x0 and sequence {ηt} ⊂ (0, ∞).
Step t = 0, 1, . . . , T: Sample gt = g(xt). Set xt+1 = proxηtr(xt − ηtgt)"; p.26: "we let Et[·] be
the conditional expectation given the iterates x0, . . . , xt."

`IsBiasedProxSGDRun P 𝓕 f D r B σ xbar η x₀ x g` says, on the probability space `(Ω, P)` with
filtration `𝓕`:
1. the step sizes are positive, `η t > 0`;
2. the run starts at the deterministic point `x₀`;
3. the iterate `x t` is `𝓕 t`-measurable and the oracle output `g t` is `𝓕 (t+1)`-measurable and
   square integrable;
4. (bias) almost surely `‖E[g t | 𝓕 t] − ∇f(x t)‖ ≤ B ‖x t − x̄‖`;
5. (variance) almost surely `E[‖g t − E[g t | 𝓕 t]‖² | 𝓕 t] ≤ σ²`;
6. (prox step) for every outcome, `x (t+1) = prox_{η_t r}(x t − η t g t)`, i.e. `x (t+1) ∈ D`
   minimizes `η_t r(y) + ½‖y − (x t − η t g t)‖²` over `D` (equivalently
   `r(y) + (1/(2η_t))‖y − (x t − η t g t)‖²`).

**Formalization Note.** "Sample g_t = g(x_t)" with a fresh draw is encoded by its two conditional
moment bounds given the past `𝓕 t`: a fresh draw of `g(x_t)`, drawn given the past from the oracle's
law at `x_t`, satisfies 4 and 5 with `𝓕 t = σ(g_0, …, g_{t−1})`, and the paper's `E_t` (given `x_0, …, x_t`, a smaller
σ-algebra) is recovered by the tower property. Square integrability of `g t` is what makes
`E‖g(x) − E g(x)‖²` meaningful. The prox is the minimizer predicate `GoldenRatioVI.IsProx` applied
to `η_t · r` (domain `D`); under `Assumption7ab` the minimizer exists and is unique, so this pins
down the paper's `prox`. The run is infinite (`t ∈ ℕ`); a finite run of `T + 1` steps is its
initial segment. -/
structure IsBiasedProxSGDRun {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℕ mΩ) (f : E → ℝ) (D : Set E) (r : E → ℝ) (B σ : ℝ) (xbar : E)
    (η : ℕ → ℝ) (x₀ : E) (x g : ℕ → Ω → E) : Prop where
  step_pos : ∀ t, 0 < η t
  init : ∀ ω, x 0 ω = x₀
  adapted : ∀ t, StronglyMeasurable[𝓕 t] (x t)
  oracle_measurable : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (g t)
  oracle_memLp : ∀ t, MemLp (g t) 2 P
  bias : ∀ t, ∀ᵐ ω ∂P, ‖(P[g t | 𝓕 t]) ω - gradient f (x t ω)‖ ≤ B * ‖x t ω - xbar‖
  variance : ∀ t, ∀ᵐ ω ∂P,
    (P[fun ω' => ‖g t ω' - (P[g t | 𝓕 t]) ω'‖ ^ 2 | 𝓕 t]) ω ≤ σ ^ 2
  prox_step : ∀ t ω,
    GoldenRatioVI.IsProx D (fun y => η t * r y) (x t ω - η t • g t ω) (x (t + 1) ω)

end DecDepSO


