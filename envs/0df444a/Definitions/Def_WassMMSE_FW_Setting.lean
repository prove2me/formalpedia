-- Prove2me | Definitions.Def_WassMMSE_FW_Setting
-- name    : WassMMSE_FW_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:18:23.787468+00:00
-- url     : https://prove2.me/theorems/022fa66d-e938-49e4-8e07-7d0eceadbcf7
-- title:
--   §6.1, pp. 21–23 — block feasible set, inexact oracle (6.2), Assumption 6.1 (i)–(iii), and runs of the fully adaptive Frank-Wolfe algorithm (Algorithm 1)
-- statement:
--   This file fixes the objects of Section 6.1 of Nguyen, Shafieezadeh-Abadeh, Kuhn and Mohajerin Esfahani: a convex program over a product of convex compact sets, an inexact linear-minimization oracle, three regularity conditions, and the fully adaptive Frank-Wolfe algorithm.
--
--   **Decision space.** The decision variable is $s=(s^{[1]},\dots,s^{[K]})$ with blocks $s^{[k]}\in\mathbb R^{d_k}$, and $\mathbb R^d=\mathbb R^{d_1}\times\dots\times\mathbb R^{d_K}$ carries the Euclidean norm $\|s\|^2=\sum_{k=1}^K\|s^{[k]}\|^2$.
--
--   1. **Block feasible set.** $\mathcal S=\times_{k=1}^K\mathcal S^{[k]}$, where every marginal feasible set $\mathcal S^{[k]}\subseteq\mathbb R^{d_k}$ is convex and compact.
--   2. **Objective.** $f$ is convex on $\mathcal S$ and differentiable at every point of $\mathcal S$. Its gradient is $\nabla f(s)$, and the partial gradient $\nabla_{[k]}f(s)$ is the $k$-th block of $\nabla f(s)$. The optimal value is $f^\star=\min_{s\in\mathcal S}f(s)$.
--   3. **Inexact oracle with precision $\delta\in[0,1]$.** A map $F$ with $F(s)\in\mathcal S$ for every $s\in\mathcal S$ and
--   $$(F(s)-s)^\top\nabla f(s)\le\delta\min_{z\in\mathcal S}(z-s)^\top\nabla f(s)\qquad\forall s\in\mathcal S. \tag{6.2}$$
--   4. **Assumption 6.1.**
--      - (i) $\beta$-smoothness, $\beta>0$: $\|\nabla f(s)-\nabla f(\bar s)\|\le\beta\|s-\bar s\|$ for all $s,\bar s\in\mathcal S$.
--      - (ii) $\alpha$-strong convexity of the marginal feasible sets with respect to $f$, $\alpha>0$: for all $s,\bar s\in\mathcal S$, $\theta\in[0,1]$ and $k$,
--      $$\theta s^{[k]}+(1-\theta)\bar s^{[k]}-\theta(1-\theta)\frac{\alpha}{2}\big\|s^{[k]}-\bar s^{[k]}\big\|^2\frac{\nabla_{[k]}f(s)}{\|\nabla_{[k]}f(s)\|}\in\mathcal S^{[k]}.$$
--      - (iii) $\varepsilon$-steepness, $\varepsilon>0$: $\|\nabla_{[k]}f(s)\|\ge\varepsilon$ for all $s\in\mathcal S$ and $k$.
--   5. **Frank-Wolfe quantities at a point $s$.** The search direction $d=F(s)-s$, the surrogate duality gap $g=-d^\top\nabla f(s)$, the adaptive stepsize for a trial smoothness parameter $b$, $\eta(b)=\min\{1,\,g/(b\|d\|^2)\}$, and the sufficient-decrease test (6.5):
--   $$f\big(s+\eta(b)d\big)\le f(s)-\eta(b)g+\frac{\eta(b)^2b}{2}\|d\|^2 .$$
--   6. **Runs of Algorithm 1.** Given $s_0\in\mathcal S$, $\beta_{-1}>0$, $\tau>1$ and $\zeta>1$, a run is a sequence of iterates $s_t$, smoothness parameters $\beta_t$ and stepsizes $\eta_t$ such that for every $t\ge0$: $\beta_t$ is the **smallest** element of $(\beta_{t-1}/\zeta)\cdot\{1,\tau,\tau^2,\dots\}$ that passes the test (6.5) at $s_t$; $\eta_t=\eta(\beta_t)$; and $s_{t+1}=s_t+\eta_t d_t$ with $d_t=F(s_t)-s_t$.
--
--   These objects carry the linear convergence analysis of Section 6.1 (Theorem 6.2 and Lemma 6.3).
--
--   **Formalization Note** The space is `PiLp 2` of Euclidean blocks, so the norm is the Euclidean one, not the sup norm. In (6.2) the minimum is written as "$\le\delta(z-s)^\top\nabla f(s)$ for every $z\in\mathcal S$"; this is equivalent because the minimum of a continuous linear function over the compact set $\mathcal S$ is attained and $\delta\ge0$. $f$ is a function on the whole space, differentiable at the points of $\mathcal S$, which is how the gradient on $\mathcal S$ of the page's $f:\mathcal S\to\mathbb R$ is read. Lean's conventions $x/0=0$ and $0^{-1}=0$ apply where the page's expressions are undefined: at $d=0$ the stepsize is $\eta(b)=0$ (and the test then passes at once), and in (ii) the normalized gradient is $0$ where $\nabla_{[k]}f(s)=0$, a case excluded by (iii). The run is infinite: the stopping criterion of Algorithm 1 is ignored. Each regularity condition carries its own positivity ($\beta,\alpha,\varepsilon>0$), the oracle carries $0\le\delta\le1$, and a run carries $\beta_{-1}>0$, $\tau>1$, $\zeta>1$ and $s_0\in\mathcal S$.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, pp. 21–23, (6.1), (6.2), block structure (p. 22), Assumption 6.1 (i)–(iii), (6.4), (6.5), Algorithm 1

import Mathlib

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-! Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, §6.1, pp. 21–23:
the generic convex program (6.1), the inexact oracle (6.2), the block structure, Assumption 6.1
and Algorithm 1 (the fully adaptive Frank-Wolfe algorithm). -/

/-- The decision space `ℝ^d = ℝ^{d_1} × ⋯ × ℝ^{d_K}` of §6.1 (p. 22), `s = (s^{[1]}, …, s^{[K]})`,
with the Euclidean norm `‖s‖² = ∑_k ‖s^{[k]}‖²` (`PiLp 2`, not the sup norm). The block
`s^{[k]} ∈ ℝ^{d_k}` is `s k`. -/
abbrev BlockSpace (K : ℕ) (d : Fin K → ℕ) : Type :=
  PiLp 2 (fun k : Fin K => EuclideanSpace ℝ (Fin (d k)))

/-- Standing assumption of §6.1 (p. 22): the feasible set is the Cartesian product
`𝒮 = ×_{k=1}^K 𝒮^{[k]}` of marginal feasible sets `𝒮^{[k]} ⊆ ℝ^{d_k}`, each convex and compact. -/
def IsBlockFeasibleSet {K : ℕ} {d : Fin K → ℕ} (S : Set (BlockSpace K d))
    (Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))) : Prop :=
  S = {s | ∀ k, s k ∈ Sk k} ∧ ∀ k, Convex ℝ (Sk k) ∧ IsCompact (Sk k)

/-- Standing assumption of (6.1) (p. 21): the objective `f` is convex on `𝒮` and differentiable at
every point of `𝒮` (as a function on the ambient space, so that `∇f(s)` exists for `s ∈ 𝒮`). -/
def IsConvexDiffObjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ S f ∧ ∀ s ∈ S, DifferentiableAt ℝ f s

/-- The inexact oracle (6.2) with precision `δ ∈ [0, 1]` (p. 21): `F` maps `𝒮` into `𝒮` and
`(F(s) − s)ᵀ∇f(s) ≤ δ · min_{z ∈ 𝒮} (z − s)ᵀ∇f(s)` for every `s ∈ 𝒮`. The minimum is written as
"`≤ δ (z − s)ᵀ∇f(s)` for every `z ∈ 𝒮`", which is equivalent because the minimum of the
continuous linear function over the compact set `𝒮` is attained and `δ ≥ 0`. -/
def IsInexactOracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (f : E → ℝ) (F : E → E) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 ∧
    ∀ s ∈ S, F s ∈ S ∧ ∀ z ∈ S, ⟪F s - s, gradient f s⟫ ≤ δ * ⟪z - s, gradient f s⟫

/-- Assumption 6.1 (i) (p. 22): `f` is `β`-smooth for some `β > 0`,
`‖∇f(s) − ∇f(s̄)‖ ≤ β‖s − s̄‖` for all `s, s̄ ∈ 𝒮`. -/
def IsSmoothOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (f : E → ℝ) (β : ℝ) : Prop :=
  0 < β ∧ ∀ s ∈ S, ∀ s' ∈ S, ‖gradient f s - gradient f s'‖ ≤ β * ‖s - s'‖

/-- Assumption 6.1 (ii) (p. 22): the marginal feasible sets are `α`-strongly convex with respect
to `f` for some `α > 0`:
`θs^{[k]} + (1 − θ)s̄^{[k]} − θ(1 − θ)(α/2)‖s^{[k]} − s̄^{[k]}‖² ∇_{[k]}f(s)/‖∇_{[k]}f(s)‖ ∈ 𝒮^{[k]}`
for all `s, s̄ ∈ 𝒮`, `θ ∈ [0, 1]` and `k`. The partial gradient `∇_{[k]}f(s)` is the block
`gradient f s k`. Where `∇_{[k]}f(s) = 0` the page's quotient is undefined and Lean's `0⁻¹ = 0`
makes the vector `0`; under Assumption 6.1 (iii) this case does not occur. -/
def IsStronglyConvexWrt {K : ℕ} {d : Fin K → ℕ} (S : Set (BlockSpace K d))
    (Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))) (f : BlockSpace K d → ℝ)
    (α : ℝ) : Prop :=
  0 < α ∧ ∀ s ∈ S, ∀ s' ∈ S, ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ k : Fin K,
    θ • s k + (1 - θ) • s' k
        - (θ * (1 - θ) * (α / 2) * ‖s k - s' k‖ ^ 2) • (‖gradient f s k‖⁻¹ • gradient f s k)
      ∈ Sk k

/-- Assumption 6.1 (iii) (p. 22): `f` is `ε`-steep for some `ε > 0`,
`‖∇_{[k]}f(s)‖ ≥ ε` for all `s ∈ 𝒮` and `k`. -/
def IsSteep {K : ℕ} {d : Fin K → ℕ} (S : Set (BlockSpace K d)) (f : BlockSpace K d → ℝ)
    (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ s ∈ S, ∀ k : Fin K, ε ≤ ‖gradient f s k‖

/-- The search direction `d = F(s) − s` of Algorithm 1 (p. 23). -/
def fwDirection {E : Type*} [AddCommGroup E] (F : E → E) (s : E) : E :=
  F s - s

/-- The surrogate duality gap `g = −dᵀ∇f(s)` of Algorithm 1 and Lemma 6.3 (pp. 23–24). -/
noncomputable def fwGap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (F : E → E) (s : E) : ℝ :=
  -⟪fwDirection F s, gradient f s⟫

/-- The adaptive stepsize (6.4) with the smoothness parameter `b` in place of `β` (p. 23):
`η(b) = min{1, g/(b‖d‖²)}`. At `d = 0` the page's quotient is undefined; Lean's `x / 0 = 0` gives
`η(b) = 0`. -/
noncomputable def fwStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (F : E → E) (s : E) (b : ℝ) : ℝ :=
  min 1 (fwGap f F s / (b * ‖fwDirection F s‖ ^ 2))

/-- The sufficient-decrease condition (6.5), i.e. the exit condition of the inner while loop of
Algorithm 1 (p. 23), for the trial smoothness parameter `b`:
`f(s + η(b)d) ≤ f(s) − η(b)g + (η(b)²b/2)‖d‖²`. -/
def LineSearchAccepts {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (F : E → E) (s : E) (b : ℝ) : Prop :=
  f (s + fwStep f F s b • fwDirection F s)
    ≤ f s - fwStep f F s b * fwGap f F s + fwStep f F s b ^ 2 * b / 2 * ‖fwDirection F s‖ ^ 2

/-- The previous smoothness parameter `β_{t−1}` of Algorithm 1: `β_{−1}` (the input) at `t = 0`,
and `β_{t−1}` from the sequence otherwise. -/
def prevBeta (βm1 : ℝ) (βt : ℕ → ℝ) : ℕ → ℝ
  | 0 => βm1
  | t + 1 => βt t

/-- An (infinite) run of Algorithm 1, the fully adaptive Frank-Wolfe algorithm (p. 23), with
oracle `F`, input `s₀ ∈ 𝒮`, initial smoothness parameter `β_{−1} > 0` and line-search parameters
`τ > 1`, `ζ > 1`: for every `t`,
* `β_t` is the **smallest** element of `(β_{t−1}/ζ)·{1, τ, τ², …}` satisfying (6.5): it equals
  `(β_{t−1}/ζ) τ^j` for some `j` at which (6.5) holds, and (6.5) fails at every `i < j`;
* `η_t = η(β_t) = min{1, g_t/(β_t‖d_t‖²)}`;
* `s_{t+1} = s_t + η_t d_t` with `d_t = F(s_t) − s_t`.
The stopping criterion is ignored: the run is infinite. -/
def IsFAFWRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (f : E → ℝ) (F : E → E) (βm1 τ ζ : ℝ) (s : ℕ → E) (βt ηt : ℕ → ℝ) : Prop :=
  0 < βm1 ∧ 1 < τ ∧ 1 < ζ ∧ s 0 ∈ S ∧
    ∀ t : ℕ,
      (∃ j : ℕ, βt t = prevBeta βm1 βt t / ζ * τ ^ j ∧ LineSearchAccepts f F (s t) (βt t) ∧
          ∀ i < j, ¬ LineSearchAccepts f F (s t) (prevBeta βm1 βt t / ζ * τ ^ i)) ∧
        ηt t = fwStep f F (s t) (βt t) ∧
        s (t + 1) = s t + ηt t • fwDirection F (s t)

end WassMMSE.FW


