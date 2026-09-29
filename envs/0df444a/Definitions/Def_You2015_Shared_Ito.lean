-- Prove2me | Definitions.Def_You2015_Shared_Ito
-- name    : You2015_Shared_Ito
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:31:26.080782+00:00
-- url     : https://prove2.me/theorems/05ada295-c736-4783-b013-ac5c77be779b
-- title:
--   Simple adapted integrands and the L² Itô integral ∫₀ᵗ H dW (as a relation between integrand and integral process)
-- statement:
--   This file defines the Itô integral of a vector-valued progressively measurable integrand against a real driving process, by the classical $L^2$ construction.
--
--   1. **Simple integrands.** On a horizon $[0,T]$, a simple adapted integrand is given by a partition $0=t_0\le t_1\le\dots\le t_p=T$ and square-integrable random vectors $\xi_i$, each $\mathcal F_{t_i}$-measurable; it is the process
--   $$H(s)=\sum_{i}\xi_i\,\mathbf 1_{(t_i,t_{i+1}]}(s),$$
--   and its elementary integral against a real process $W$ is
--   $$\int_0^u H\,dW=\sum_i\xi_i\big(W(t_{i+1}\wedge u)-W(t_i\wedge u)\big).$$
--
--   2. **Itô integral.** A process $J$ is an Itô integral $J(t)=\int_0^t H(s)\,dW(s)$, $t\ge0$, when $H$ is progressively measurable with $\mathbb E\int_0^T|H(s)|^2ds<\infty$ for every $T$, $J$ is adapted, and for every horizon $T$ there are simple adapted integrands $H_k$ on $[0,T]$ with
--   $$\mathbb E\int_0^T|H_k(s)-H(s)|^2\,ds\to0\quad\text{and}\quad\mathbb E\Big|\int_0^t H_k\,dW-J(t)\Big|^2\to0\ \ \text{for every }t\in[0,T].$$
--
--   When $W$ is an $\{\mathcal F_t\}$-Brownian motion this determines $J(t)$ almost surely for each $t$; it is the Itô integral of Mao's and Mao–Yuan's monographs, which the paper uses. The definition is a relation between integrand and integral rather than an operator, so no junk value is ever produced.
--
--   Used by both missions of this paper: 01-asymptotic-stability (Theorem 3.4 series; pp. 907–908, the stochastic integral in (2.1)) and 02-exponential-stability (Theorem 4.2 series; pp. 907–908, the stochastic integral in (2.1)).
--
--   **Formalization Note** Expectations and time integrals are lower Lebesgue integrals with values in $[0,\infty]$. The partition is only required to be non-decreasing; empty intervals contribute nothing.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, pp. 907–908, the stochastic integral in (2.1) (the Itô integral of the paper's references [15, 23])

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Shared

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A simple adapted `E`-valued integrand on `[0, T]`: a partition
`0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_p = T` and square-integrable random vectors `ξᵢ`, each
`𝓕_{tᵢ}`-measurable; the process is `∑ᵢ ξᵢ 1_{(tᵢ, tᵢ₊₁]}`. -/
structure SimpleIntegrand (E : Type*) [NormedAddCommGroup E] (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (T : ℝ≥0) where
  p : ℕ
  t : Fin (p + 1) → ℝ≥0
  mono : Monotone t
  start : t 0 = 0
  finish : t (Fin.last p) = T
  ξ : Fin p → Ω → E
  meas : ∀ i, StronglyMeasurable[𝓕 (t i.castSucc)] (ξ i)
  sq : ∀ i, ∫⁻ ω, ‖ξ i ω‖ₑ ^ 2 ∂P < ⊤

namespace SimpleIntegrand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {T : ℝ≥0}

/-- The value `∑ᵢ 1_{(tᵢ, tᵢ₊₁]}(s) ξᵢ(ω)` of a simple integrand. -/
noncomputable def eval (H : SimpleIntegrand E 𝓕 P T) (s : ℝ≥0) (ω : Ω) : E :=
  ∑ i : Fin H.p, if H.t i.castSucc < s ∧ s ≤ H.t i.succ then H.ξ i ω else 0

/-- The elementary stochastic integral `∫₀ᵘ H dW = ∑ᵢ (W(tᵢ₊₁ ∧ u) − W(tᵢ ∧ u)) ξᵢ`
against a real process `W`. -/
noncomputable def integral (H : SimpleIntegrand E 𝓕 P T) (W : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : Ω) : E :=
  ∑ i : Fin H.p, (W (min (H.t i.succ) u) ω - W (min (H.t i.castSucc) u) ω) • H.ξ i ω

end SimpleIntegrand

/-- `J(t) = ∫₀ᵗ H(s) dW(s)`, `t ≥ 0`, is an L² Itô integral process of the `E`-valued integrand
`H` against the real process `W`: `H` is progressively measurable for `{𝓕_t}` with
`E ∫₀ᵀ |H(s)|² ds < ∞` for every `T`, `J` is adapted, and for every horizon `T` some sequence
of simple adapted integrands `Hₖ` on `[0, T]` satisfies `E ∫₀ᵀ |Hₖ − H|² ds → 0` and, for every
`t ∈ [0, T]`, `E |∫₀ᵗ Hₖ dW − J(t)|² → 0`. Expectations and time integrals are lower Lebesgue
integrals in `[0, ∞]`. -/
def IsItoIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (H J : ℝ≥0 → Ω → E) :
    Prop :=
  IsStronglyProgressive 𝓕 H ∧
    (∀ T : ℝ≥0, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖H s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤) ∧
    StronglyAdapted 𝓕 J ∧
    ∀ T : ℝ≥0, ∃ Hs : ℕ → SimpleIntegrand E 𝓕 P T,
      Tendsto (fun k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ‖(Hs k).eval s.toNNReal ω - H s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P) atTop (𝓝 0) ∧
      ∀ t ≤ T, Tendsto (fun k => ∫⁻ ω, ‖(Hs k).integral W t ω - J t ω‖ₑ ^ 2 ∂P)
          atTop (𝓝 0)

end You2015.Shared


