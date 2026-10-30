-- Prove2me | Definitions.Def_MultimodalPricing_Regret_Regret
-- name    : MultimodalPricing_Regret_Regret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:04:00.632992+00:00
-- url     : https://prove2.me/theorems/4e5f1cad-ebbf-4938-a855-c6b24c4e47d8
-- title:
--   Realized fixed-price benchmark and local pseudo-regret
-- statement:
--   A response field $D_n(p,\omega)$ gives counterfactual demands at every real price in the interval. Each fixed-price section is measurable, integrable and has mean $f(p)$; simultaneously all demands are in $[0,1]$ almost surely, and actual observed demand equals $D_n(p_n,\omega)$. The actual process separately satisfies the sequential kernel law. No sample-path continuity or uniform concentration is assumed.
--
--   The literal realized benchmark is
--   $$R_T(\omega)=\sup_{p\in[a,b]}\sum_{n<T}pD_n(p,\omega)-\sum_{n<T}p_n(\omega)d_n(\omega).$$
--   All couplings satisfying these conditions are admitted. For Lemma 3 only, the average pseudo-regret is $t^{-1}\sum_{n<t}[\sup_{p\in[a,b]}pf(p)-p_n f(p_n)]$. It is not substituted for the goal's realized regret. The bounded demands make the realized supremum finite on a common full-measure set; outer probability handles its possibly nonmeasurable bad event.
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), regret display, printed/PDF p. 9; Lemma 3, p. 14

import Definitions.Def_MultimodalPricing_Regret_Algorithm

open MeasureTheory

noncomputable section

namespace MultimodalPricing.Regret

/-- All couplings of bounded potential responses are admitted. Each fixed price has
mean f, and the actual observations coincide with the response at the posted price.
Only actual observations obey the sequential kernel law; no uniform concentration or
sample-path regularity is imposed on the counterfactual field. -/
def IsResponseField {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℕ) (a b : ℝ) (f : ℝ → ℝ) (O : Observation Ω)
    (D : ℕ → ℝ → Ω → ℝ) : Prop :=
  (∀ n < T, ∀ p ∈ Set.Icc a b, Measurable (D n p) ∧
    Integrable (D n p) μ ∧ (∫ ω, D n p ω ∂μ) = f p) ∧
  (∀ᵐ ω ∂μ, ∀ n < T,
    (∀ p ∈ Set.Icc a b, D n p ω ∈ Set.Icc (0 : ℝ) 1) ∧
    O.demand n ω = D n (O.price n ω) ω)

/-- Literal p. 9 supremum of realized fixed-price revenues, on the same sample path. -/
def realizedRegret {Ω : Type*} (T : ℕ) (a b : ℝ)
    (p d : ℕ → Ω → ℝ) (D : ℕ → ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  sSup ((fun q => ∑ n ∈ Finset.range T, q * D n q ω) '' Set.Icc a b) -
    ∑ n ∈ Finset.range T, p n ω * d n ω

/-- Used only for within-bin performance, never as the goal's benchmark. -/
def averagePseudoRegret {Ω : Type*} (t : ℕ) (a b : ℝ) (f : ℝ → ℝ)
    (p : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ n ∈ Finset.range t, (bestReward a b f - reward f (p n ω))) / t

end MultimodalPricing.Regret


