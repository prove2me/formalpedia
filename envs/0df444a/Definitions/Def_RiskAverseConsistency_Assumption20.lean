-- Prove2me | Definitions.Def_RiskAverseConsistency_Assumption20
-- name    : RiskAverseConsistency_Assumption20
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:55.266251+00:00
-- url     : https://prove2.me/theorems/6720e63d-7e6a-4cfb-8ee6-211df1fcb4ed
-- title:
--   Assumption 20 (hypotheses of the epigraphical law of large numbers)
-- statement:
--   **Assumption 20** requires: $(\Omega,\mathcal F,P)$ is a nonatomic, complete probability space and $(\Theta,\Sigma,\mathbb M)$ a complete probability space; $\zeta:\Omega\to\Theta$ is a random element with distribution $\mathbb M$; $\zeta^1,\zeta^2,\dots$, defined on a complete probability space $(\Omega',\mathcal F',P')$, are i.i.d. $\Theta$-valued random elements each distributed as $\zeta$; $(V,d_V)$ is a complete separable metric space and $1\le p<\infty$; and
--
--   1. ($\mathfrak R1$) $\Psi:V\times\Theta\to\mathbb R$ is random lower semicontinuous: jointly measurable for the product of the Borel $\sigma$-algebra of $V$ and $\Sigma$, with $\Psi(\cdot,\theta)$ lower semicontinuous for every $\theta$;
--   2. ($\mathfrak R2$) $\Psi_v=\Psi(v,\cdot)\in L^p(\Theta,\Sigma,\mathbb M)$ for each $v\in V$;
--   3. ($\mathfrak R3$) every $\bar v\in V$ has a neighborhood $\mathcal V_{\bar v}$ and some $h\in L^p(\Theta,\Sigma,\mathbb M)$ with $\Psi(v,\cdot)\ge h(\cdot)$ for all $v\in\mathcal V_{\bar v}$.
--
--   **Formalization Note** Samples are indexed from $0$; independence is `ProbabilityTheory.iIndepFun`; nonatomic is `IsNonatomic`. The Borel $\sigma$-algebra of $V$ is the instance `[BorelSpace V]`.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.16, Assumption 20; p.4 (random lower semicontinuity)

import Mathlib
import Definitions.Def_RiskAverseConsistency_IsNonatomic

open MeasureTheory Topology

namespace RiskAverseConsistency

/-- **Assumption 20** of Milz–Surowiec: `(Ω, F, P)` is a nonatomic, complete probability space;
`(Θ, Σ, 𝕄)` is a complete probability space; `ζ : Ω → Θ` is a random element with distribution `𝕄`;
`ζ¹, ζ², …`, defined on a complete probability space `(Ω′, F′, P′)`, are independent identically
distributed `Θ`-valued random elements each with the distribution of `ζ`; `(V, d_V)` is a complete,
separable metric space and `1 ≤ p < ∞`; and
* (ℜ1) `Ψ : V × Θ → ℝ` is random lower semicontinuous (jointly measurable for the product of the
  Borel σ-algebra of `V` and `Σ`, and `Ψ(·, θ)` lower semicontinuous for every `θ`);
* (ℜ2) for each `v ∈ V`, `Ψ_v(·) := Ψ(v, ·) ∈ Lᵖ(Θ, Σ, 𝕄)`;
* (ℜ3) for each `v̄ ∈ V` there exist a neighborhood `𝒱_v̄ ⊂ V` of `v̄` and `h ∈ Lᵖ(Θ, Σ, 𝕄)` with
  `Ψ(v, ·) ≥ h(·)` for all `v ∈ 𝒱_v̄`.

Milz, Surowiec, arXiv:2207.14756v2, Assumption 20, p.16; random lower semicontinuity, p.4.

Formalization Note: the Borel σ-algebra of `V` is the instance `[BorelSpace V]`. The samples are
indexed `ζs 0, ζs 1, …` (the paper's `ζ¹, ζ², …`); "independent" is `ProbabilityTheory.iIndepFun`.
Nonatomic is the classical notion `IsNonatomic`. -/
structure Assumption20 {Ω Θ Ω' V : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace Ω'] [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure Ω) (𝕄 : Measure Θ) (ζ : Ω → Θ) (P' : Measure Ω') (ζs : ℕ → Ω' → Θ)
    (p : ENNReal) (Ψ : V → Θ → ℝ) : Prop where
  P_prob : IsProbabilityMeasure P
  P_nonatomic : IsNonatomic P
  P_complete : P.IsComplete
  𝕄_prob : IsProbabilityMeasure 𝕄
  𝕄_complete : 𝕄.IsComplete
  ζ_measurable : Measurable ζ
  ζ_law : P.map ζ = 𝕄
  P'_prob : IsProbabilityMeasure P'
  P'_complete : P'.IsComplete
  ζs_measurable : ∀ i, Measurable (ζs i)
  ζs_indep : ProbabilityTheory.iIndepFun ζs P'
  ζs_law : ∀ i, P'.map (ζs i) = P.map ζ
  V_complete : CompleteSpace V
  V_separable : TopologicalSpace.SeparableSpace V
  one_le_p : 1 ≤ p
  p_ne_top : p ≠ ⊤
  R1_measurable : Measurable (Function.uncurry Ψ)
  R1_lsc : ∀ θ : Θ, LowerSemicontinuous (fun v => Ψ v θ)
  R2 : ∀ v : V, MemLp (Ψ v) p 𝕄
  R3 : ∀ v₁ : V, ∃ 𝒱 ∈ 𝓝 v₁, ∃ h : Θ → ℝ, MemLp h p 𝕄 ∧ ∀ v ∈ 𝒱, ∀ θ : Θ, h θ ≤ Ψ v θ

end RiskAverseConsistency


