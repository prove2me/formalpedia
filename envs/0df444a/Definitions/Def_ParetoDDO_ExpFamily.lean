-- Prove2me | Definitions.Def_ParetoDDO_ExpFamily
-- name    : ParetoDDO_ExpFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:15.24418+00:00
-- url     : https://prove2.me/theorems/a3be01ba-99ce-46ee-b1e6-11e070a75176
-- title:
--   Log-MGFs, the exponential family (Assumption 4.1), Assumption 4.2 and the Gärtner–Ellis rate (4.4)
-- statement:
--   Let $\widehat S$ be a statistic in $\mathbb R^d$ and $\mathbb P^T_\theta$ the restriction of $\mathbb P_\theta$ to $\mathcal F_T$.
--
--   1. **Log-MGF.** $\Lambda_T(\lambda,\theta)=\log\mathbb E_\theta[\exp\langle\lambda,\widehat S_T\rangle]$ if the expectation is finite, $+\infty$ otherwise.
--   2. **Assumption 4.1 (time-homogeneous exponential family).** There are $\bar\theta\in\Theta$ and a continuous $g:\Theta\to\mathbb R^d$ such that, with $A_T(\lambda)=\Lambda_T(\lambda,\bar\theta)$, $Tg(\theta)\in\operatorname{dom}A_T$ and
--   $$
--   \frac{d\mathbb P^T_\theta}{d\mathbb P^T_{\bar\theta}}=\exp\big(\langle Tg(\theta),\widehat S_T\rangle-A_T(Tg(\theta))\big)\qquad\forall T\in\mathbb N,\ \theta\in\Theta. \tag{4.1}
--   $$
--   3. **Assumption 4.2.** $\Lambda_T(\lambda,\theta)<\infty$ for all $\lambda$, $T$; the limit $\Lambda(\lambda,\theta)=\lim_{T}\frac1T\Lambda_T(T\lambda,\theta)$ exists in $(-\infty,\infty]$; $0\in\operatorname{int}\operatorname{dom}\Lambda(\cdot,\theta)$; $\nabla_\lambda\Lambda(\lambda,\theta)$ exists on $\operatorname{int}\operatorname{dom}\Lambda(\cdot,\theta)$ and its norm tends to $\infty$ as $\lambda$ approaches the boundary of the domain; all for $\theta\in\Theta$.
--   4. **The Gärtner–Ellis rate (4.4).** $I(s,\theta)=\sup_{\lambda\in\mathbb R^d}\langle\lambda,s\rangle-\Lambda(\lambda,\theta)$.
--
--   Assumption 4.1 makes $\widehat S$ a sufficient statistic; Assumption 4.2 gives it an LDP.
--
--   **Formalization Note** `logMGF μ Y u` is $(-\infty,\infty]$-valued (`EReal`). The density (4.1) is stated setwise: $\mathbb P_\theta(A)=\int_A\exp(\langle Tg(\theta),\widehat S_T\rangle-A_T(Tg(\theta)))\,d\mathbb P_{\bar\theta}$ for every $A\in\mathcal F_T$, $T\ge1$, which is the Radon–Nikodym identity of the restrictions. `IsExpFamily … θbar g` is (4.1) for a given $\bar\theta$, $g$; Assumption 4.1 is its existential closure. `IsLogMGFRegular … Λ` is Assumption 4.2 for a given $\Lambda$; the gradient is that of the real-valued $\Lambda(\cdot,\theta)$ on the interior of its domain, and steepness is stated along the interior at every boundary point of the domain.
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Λ_T, P^T_θ and Assumption 4.1, (4.1), p.23; Assumption 4.2, (4.3), p.23; (4.4), p.24

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

variable {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}

open Classical in
/-- The log-moment generating function of a random vector (arXiv:2010.06606v4, p.23):
`Λ_T(λ, θ) = log E_θ[exp⟨λ, Ŝ_T⟩]` if the expectation is finite and `+∞` otherwise, here for a
general measure `μ` and random vector `Y`.

**Formalization Note** For a probability measure the expectation of the positive function
`exp⟨λ, Y⟩` is finite exactly when it is integrable; it is then positive, so `Real.log` is applied
to a positive number. The value lies in `(−∞, +∞]` (`EReal`). -/
noncomputable def logMGF (μ : Measure Ω) (Y : Ω → Vec d) (u : Vec d) : EReal :=
  if Integrable (fun ω => Real.exp ⟪u, Y ω⟫) μ then
    ((Real.log (∫ ω, Real.exp ⟪u, Y ω⟫ ∂μ) : ℝ) : EReal)
  else ⊤

/-- **Assumption 4.1** (time-homogeneous exponential family of stochastic processes;
arXiv:2010.06606v4, (4.1), p.23), for a given baseline model `θ̄` and parametrization `g`:
`θ̄ ∈ Θ`, `g : Θ → ℝ^d` is continuous, `T g(θ) ∈ dom A_T` where `A_T(λ) = Λ_T(λ, θ̄)`, and
`dP^T_θ / dP^T_θ̄ = exp(⟨T g(θ), Ŝ_T⟩ − A_T(T g(θ)))` for all `T` and `θ ∈ Θ`, where `P^T_θ` is the
restriction of `P_θ` to `F_T`.

**Formalization Note** The Radon–Nikodym identity of the restrictions to `F_T` is written setwise:
`P_θ(A) = ∫_A exp(⟨T g(θ), Ŝ_T⟩ − A_T(T g(θ))) dP_θ̄` for every `A ∈ F_T`. `A_T(T g(θ))` is finite
by the domain condition, so its real value is used. Assumption 4.1 itself is `∃ θ̄ g, IsExpFamily …`.
Time is `T ∈ {1, 2, …}`. -/
structure IsExpFamily (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (Ŝ : ℕ → Ω → Vec d) (θbar : Vec d) (g : Vec d → Vec d) : Prop where
  /-- The baseline model lies in `Θ`. -/
  base_mem : θbar ∈ Θ
  /-- `g` is continuous on `Θ`. -/
  continuousOn : ContinuousOn g Θ
  /-- `T g(θ) ∈ dom A_T`. -/
  mem_dom : ∀ θ ∈ Θ, ∀ T : ℕ, 1 ≤ T → logMGF (P θbar) (Ŝ T) ((T : ℝ) • g θ) ≠ ⊤
  /-- The density (4.1) of `P^T_θ` with respect to `P^T_θ̄`. -/
  density : ∀ θ ∈ Θ, ∀ T : ℕ, 1 ≤ T → ∀ A : Set Ω, MeasurableSet[histSigma ξ T] A →
    P θ A = ∫⁻ ω in A, ENNReal.ofReal (Real.exp (⟪(T : ℝ) • g θ, Ŝ T ω⟫ -
      (logMGF (P θbar) (Ŝ T) ((T : ℝ) • g θ)).toReal)) ∂(P θbar)

/-- **Assumption 4.2** (log-moment generating functions; arXiv:2010.06606v4, (4.3), p.23), for a given
`Λ : ℝ^d × Θ → (−∞, ∞]`: `Λ_T(λ, θ) < ∞` for all `λ` and `T`; `Λ(λ, θ) = lim_T (1/T) Λ_T(Tλ, θ)`
exists in `(−∞, ∞]`; the origin lies in the interior of `dom Λ(·, θ)`; the gradient `∇_λ Λ(λ, θ)`
exists on the interior of the domain, and its norm tends to `∞` as `λ` approaches the boundary of the
domain; all for every `θ ∈ Θ`.

**Formalization Note** `dom Λ(·, θ) = {λ : Λ(λ, θ) < ∞}`. On the interior of the domain `Λ(·, θ)` is
finite, and the gradient is that of its real-valued version (`EReal.toReal`). Steepness is stated at
every boundary point `λ₀` of the domain, along `λ → λ₀` inside the interior. -/
structure IsLogMGFRegular (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (Ŝ : ℕ → Ω → Vec d)
    (Λ : Vec d → Vec d → EReal) : Prop where
  /-- `Λ_T(λ, θ) < ∞`. -/
  finite : ∀ θ ∈ Θ, ∀ T : ℕ, 1 ≤ T → ∀ u : Vec d, logMGF (P θ) (Ŝ T) u ≠ ⊤
  /-- (4.3): `Λ(λ, θ) = lim_T (1/T) Λ_T(Tλ, θ)`. -/
  tendsto : ∀ θ ∈ Θ, ∀ u : Vec d,
    Tendsto (fun T : ℕ => (((T : ℝ)⁻¹ : ℝ) : EReal) * logMGF (P θ) (Ŝ T) ((T : ℝ) • u)) atTop
      (𝓝 (Λ u θ))
  /-- `Λ` takes values in `(−∞, ∞]`. -/
  ne_bot : ∀ θ ∈ Θ, ∀ u : Vec d, Λ u θ ≠ ⊥
  /-- `0 ∈ int dom Λ(·, θ)`. -/
  zero_mem_interior : ∀ θ ∈ Θ, (0 : Vec d) ∈ interior {u | Λ u θ ≠ ⊤}
  /-- `∇_λ Λ(λ, θ)` exists on `int dom Λ(·, θ)`. -/
  differentiableAt : ∀ θ ∈ Θ, ∀ u ∈ interior {u : Vec d | Λ u θ ≠ ⊤},
    DifferentiableAt ℝ (fun v => (Λ v θ).toReal) u
  /-- `‖∇_λ Λ(λ, θ)‖ → ∞` as `λ` approaches the boundary of `dom Λ(·, θ)`. -/
  steep : ∀ θ ∈ Θ, ∀ u₀ ∈ frontier {u : Vec d | Λ u θ ≠ ⊤},
    Tendsto (fun u => ‖gradient (fun v => (Λ v θ).toReal) u‖)
      (𝓝[interior {u : Vec d | Λ u θ ≠ ⊤}] u₀) atTop

/-- The Gärtner–Ellis rate function **(4.4)** (arXiv:2010.06606v4, p.24):
`I(s, θ) = sup_{λ ∈ ℝ^d} ⟨λ, s⟩ − Λ(λ, θ)`, the convex conjugate of `Λ(·, θ)`, in `[−∞, ∞]`. -/
noncomputable def gartnerEllisRate (Λ : Vec d → Vec d → EReal) (s θ : Vec d) : EReal :=
  ⨆ u : Vec d, ((⟪u, s⟫ : ℝ) : EReal) - Λ u θ

end ParetoDDO


