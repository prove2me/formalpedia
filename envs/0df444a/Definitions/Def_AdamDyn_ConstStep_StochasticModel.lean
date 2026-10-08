-- Prove2me | Definitions.Def_AdamDyn_ConstStep_StochasticModel
-- name    : AdamDyn_ConstStep_StochasticModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:59.260366+00:00
-- url     : https://prove2.me/theorems/d0a1ecce-99e0-4645-a4e4-7c62fece26d9
-- title:
--   Assumptions 2.2, 2.5, 4.1, 4.2 ii), the objective $F$, $S$ (2.2), the mean field $h_\gamma$ (3.2), the noise $\Delta^{\gamma,R}$, uniform integrability and tightness
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $(\Xi,\mathfrak S)$ a measurable space, $\mu$ the law of a $\Xi$-valued random variable $\xi$, $f:\mathbb R^d\times\Xi\to\mathbb R$, and $\nabla f(x,\xi)$ its gradient in $x$.
--
--   **Assumption 2.2.** (i) $f(x,\cdot)$ is measurable for every $x$ (as is $\nabla f(x,\cdot)$); (ii) for $\mu$-almost every $\xi$, $f(\cdot,\xi)$ is continuously differentiable with gradient $\nabla f(\cdot,\xi)$; (iii) some $x_*$ has $\mathbb E|f(x_*,\xi)|<\infty$ and $\mathbb E\|\nabla f(x_*,\xi)\|^2<\infty$; (iv) for every compact $K$ there is $L_K>0$ with $\mathbb E\|\nabla f(x,\xi)-\nabla f(y,\xi)\|^2 \le L_K^2\|x-y\|^2$ for $x,y\in K$.
--
--   The **objective** and the **second-moment map** are (2.2)
--
--   $$
--   F(x) := \mathbb E\, f(x,\xi), \qquad S(x) := \mathbb E\, \nabla f(x,\xi)^{\odot 2}.
--   $$
--
--   **Assumption 2.5.** $\bar\alpha,\bar\beta:\mathbb R_+\to[0,1)$, the limits $a := \lim_{\gamma\downarrow0}(1-\bar\alpha(\gamma))/\gamma$ and $b := \lim_{\gamma\downarrow0}(1-\bar\beta(\gamma))/\gamma$ exist, $a>0$, $b>0$ and $b\le 4a$.
--
--   **Assumption 4.1.** The samples $(\xi_n)_{n\ge1}$ are independent and each has law $\mu$.
--
--   **Assumption 4.2 ii)** (with parameter $p$). For every compact $K\subset\mathbb R^d$ there is $p_K>p$ with $\sup_{x\in K}\mathbb E\|\nabla f(x,\xi)\|^{p_K}<\infty$.
--
--   The **mean field** is $h_\gamma(n,z) := \gamma^{-1}\mathbb E\big(T_{\gamma,\bar\alpha(\gamma),\bar\beta(\gamma)}(n,z,\xi)-z\big)$ (3.2). With $\mathcal F_n := \sigma(\xi_1,\dots,\xi_n)$, the **noise** of the truncated iterates is
--
--   $$
--   \Delta^{\gamma,R}_{n+1} := \gamma^{-1}(z^{\gamma,R}_{n+1}-z^{\gamma,R}_n) - \mathbb E\big(\gamma^{-1}(z^{\gamma,R}_{n+1}-z^{\gamma,R}_n)\,\big|\,\mathcal F_n\big).
--   $$
--
--   A family $(X_i)_{i\in I}$ of $\mathcal Z$-valued random variables is **uniformly integrable** if $\lim_{A\to+\infty}\sup_{i\in I}\mathbb E(\|X_i\|\mathbb 1_{\|X_i\|>A}) = 0$. A family $(X_\alpha)$ of random continuous paths $[0,+\infty)\to\mathcal Z$ is **tight** (bounded in probability) if for every $\delta>0$ there is a compact set $K$ of $C([0,+\infty),\mathcal Z)$, with the topology of uniform convergence on compact intervals, such that $\mathbb P(X_\alpha\in K)\ge 1-\delta$ for every $\alpha$.
--
--   These are the probabilistic hypotheses and objects of the paper's constant-step analysis.
--
--   **Formalization Note** $\nabla f$ is a given function `gf` that coincides with the gradient of $f(\cdot,\xi)$ for $\mu$-almost every $\xi$; its measurability in $\xi$ is the standing convention behind the paper's expectations of $\nabla f$. Moments and the uniform-integrability expectations are lower Lebesgue integrals in $[0,+\infty]$, so they are never silently replaced by $0$. Independence is `iIndepFun` of $(\xi_{n+1})_{n\in\mathbb N}$ and the conditional expectation is Mathlib's `condExp`. A path belongs to $K$ when its restriction to $[0,+\infty)$ is an element of $K$; the compact-open topology on $C([0,+\infty),\mathcal Z)$ is the topology of uniform convergence on compacts.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3, Assumption 2.2 and Eq. (2.2); p. 4, Assumption 2.5 and Eq. (3.2); p. 5, F_n; p. 6, Assumptions 4.1, 4.2; p. 7, tightness; p. 22, uniform integrability and Δ^{γ,R}

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_adamMap

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

variable {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]

/-- Assumption 2.2, p. 3, for the integrand `f : ℝ^d × Ξ → ℝ` and the law `μ` of `ξ`, with the
stochastic gradient `∇f(x, ξ)` given as `gf x ξ`:
i) `f(x, ·)` is measurable for every `x` (and so is `∇f(x, ·)`, which the paper integrates);
ii) for `μ`-almost every `ξ`, `f(·, ξ)` is continuously differentiable with gradient `gf(·, ξ)`;
iii) some `x*` has `E|f(x*, ξ)| < ∞` and `E‖∇f(x*, ξ)‖² < ∞`;
iv) for every compact `K` there is `L_K > 0` with
`E‖∇f(x, ξ) − ∇f(y, ξ)‖² ≤ L_K² ‖x − y‖²` for `x, y ∈ K`. -/
structure Assumption22 (μ : Measure Ξ) (f : E d → Ξ → ℝ) (gf : E d → Ξ → E d) : Prop where
  measurable_f : ∀ x, Measurable (fun ξ => f x ξ)
  measurable_gf : ∀ x, Measurable (fun ξ => gf x ξ)
  contDiff_ae : ∀ᵐ ξ ∂μ, ContDiff ℝ 1 (fun x => f x ξ) ∧
    ∀ x, gradient (fun y => f y ξ) x = gf x ξ
  moment_at : ∃ xs : E d, Integrable (fun ξ => f xs ξ) μ ∧ ∫⁻ ξ, ‖gf xs ξ‖ₑ ^ 2 ∂μ < ⊤
  lipschitz_L2 : ∀ K : Set (E d), IsCompact K → ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
    ∫⁻ ξ, ‖gf x ξ - gf y ξ‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (L ^ 2 * ‖x - y‖ ^ 2)

/-- The objective `F(x) := E(f(x, ξ))` of (2.2), p. 3. -/
noncomputable def objective (μ : Measure Ξ) (f : E d → Ξ → ℝ) (x : E d) : ℝ :=
  ∫ ξ, f x ξ ∂μ

/-- `S(x) := E(∇f(x, ξ)^{⊙2})` of (2.2), p. 3 (coordinatewise square). -/
noncomputable def sqGradMean (μ : Measure Ξ) (gf : E d → Ξ → E d) (x : E d) : E d :=
  ∫ ξ, (WithLp.toLp 2 (fun i => gf x ξ i ^ 2) : E d) ∂μ

/-- Assumption 2.5, p. 4: `ᾱ, β̄ : ℝ₊ → [0, 1)` with `a := lim_{γ↓0} (1 − ᾱ(γ))/γ` and
`b := lim_{γ↓0} (1 − β̄(γ))/γ` existing, `a > 0`, `b > 0`, `b ≤ 4a`. -/
structure Assumption25 (αbar βbar : ℝ → ℝ) (a b : ℝ) : Prop where
  αbar_mem : ∀ γ : ℝ, 0 ≤ γ → 0 ≤ αbar γ ∧ αbar γ < 1
  βbar_mem : ∀ γ : ℝ, 0 ≤ γ → 0 ≤ βbar γ ∧ βbar γ < 1
  tendsto_a : Tendsto (fun γ => (1 - αbar γ) / γ) (𝓝[>] 0) (𝓝 a)
  tendsto_b : Tendsto (fun γ => (1 - βbar γ) / γ) (𝓝[>] 0) (𝓝 b)
  a_pos : 0 < a
  b_pos : 0 < b
  b_le : b ≤ 4 * a

/-- Assumption 4.1, p. 6: the samples `(ξ_n : n ≥ 1)` are iid with the law `μ` of `ξ`
(`ξ 0` is unused). -/
def Assumption41 (P : Measure Ω) (μ : Measure Ξ) (ξ : ℕ → Ω → Ξ) : Prop :=
  (∀ n, Measurable (ξ n)) ∧ iIndepFun (fun n => ξ (n + 1)) P ∧ ∀ n, P.map (ξ (n + 1)) = μ

/-- Assumption 4.2 ii), p. 6: for every compact `K ⊂ ℝ^d` there is `p_K > p` with
`sup_{x ∈ K} E(‖∇f(x, ξ)‖^{p_K}) < ∞` (moments as lower Lebesgue integrals in `[0, ∞]`). -/
def Assumption42ii (μ : Measure Ξ) (gf : E d → Ξ → E d) (p : ℝ) : Prop :=
  ∀ K : Set (E d), IsCompact K → ∃ pK : ℝ, p < pK ∧
    (⨆ x ∈ K, ∫⁻ ξ, ‖gf x ξ‖ₑ ^ pK ∂μ) < ⊤

/-- The mean field `h_γ(n, z) := γ⁻¹ E(T_{γ,ᾱ(γ),β̄(γ)}(n, z, ξ) − z)` of (3.2), p. 4. -/
noncomputable def hGamma (μ : Measure Ξ) (gf : E d → Ξ → E d) (αbar βbar : ℝ → ℝ) (ε γ : ℝ)
    (n : ℕ) (z : Z d) : Z d :=
  γ⁻¹ • ∫ ξ, (adamMap gf γ (αbar γ) (βbar γ) ε n z ξ - z) ∂μ

/-- `ℱ_n`, the σ-algebra generated by `ξ_1, …, ξ_n` (p. 5); `ℱ_0` is trivial. -/
abbrev natFiltration (ξ : ℕ → Ω → Ξ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ k ∈ Finset.Icc 1 n, MeasurableSpace.comap (ξ k) inferInstance

/-- The noise `Δ^{γ,R}_{n+1} := γ⁻¹(z^{γ,R}_{n+1} − z^{γ,R}_n) − E(γ⁻¹(z^{γ,R}_{n+1} − z^{γ,R}_n) | ℱ_n)`,
p. 22, as a random variable (`noise … n` is `Δ^{γ,R}_{n+1}`). -/
noncomputable def noise (P : Measure Ω) (ξ : ℕ → Ω → Ξ) (gf : E d → Ξ → E d)
    (αbar βbar : ℝ → ℝ) (ε γ R : ℝ) (x0 : E d) (n : ℕ) : Ω → Z d :=
  fun ω => truncIncr gf αbar βbar ε γ R x0 (fun k => ξ k ω) n -
    (P[fun ω' => truncIncr gf αbar βbar ε γ R x0 (fun k => ξ k ω') n | natFiltration ξ n]) ω

/-- Uniform integrability in the sense of p. 22: a family `(X_i : i ∈ I)` of random variables on
`𝒵` is uniformly integrable if `lim_{A→+∞} sup_{i ∈ I} E(‖X_i‖ 1_{‖X_i‖ > A}) = 0`
(expectations as lower Lebesgue integrals in `[0, ∞]`). -/
def IsUnifIntegrable (P : Measure Ω) {ι : Type*} (X : ι → Ω → Z d) : Prop :=
  Tendsto (fun A : ℝ => ⨆ i, ∫⁻ ω, {ω | A < zNorm (X i ω)}.indicator
      (fun ω => ENNReal.ofReal (zNorm (X i ω))) ω ∂P) atTop (𝓝 0)

/-- Tightness (boundedness in probability) of a family of random continuous paths, p. 7: for every
`δ > 0` there is a compact set `K` of `C([0, +∞), 𝒵)` (topology of uniform convergence on
compact intervals = compact-open topology) with `P(X_α ∈ K) ≥ 1 − δ` for every `α`. A path
`X_α(ω) : ℝ → 𝒵` lies in `K` when its restriction to `[0, +∞)` is an element of `K`. -/
def IsTight (P : Measure Ω) {ι : Type*} (X : ι → Ω → ℝ → Z d) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : Set C(Set.Ici (0 : ℝ), Z d), IsCompact K ∧
    ∀ α, ENNReal.ofReal (1 - δ) ≤ P {ω | ∃ g ∈ K, ∀ t : Set.Ici (0 : ℝ), g t = X α ω t}

end AdamDyn.ConstStep


