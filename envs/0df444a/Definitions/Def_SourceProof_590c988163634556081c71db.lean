-- Prove2me | Definitions.Def_SourceProof_590c988163634556081c71db
-- name    : SourceProof_590c988163634556081c71db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:00:56.678185+00:00
-- url     : https://prove2.me/theorems/2a92c0f6-f4a7-45e2-a0b5-81d01336ee69
-- title:
--   LevyStochCalc source module: SourceProof_590c988163634556081c71db
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.stepIntegral_ae_eq_integral_sub` comes from the `LevyStochCalc.Poisson.CompensatedProfileRaw` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRaw_F000

open private setIntegral_indicator_snd from Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRaw_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of an integrable mark profile is pathwise

Let `N` be a Poisson random measure on `[0, ∞) × E` with `σ`-finite intensity `ν`, possibly
`ν(E) = ∞`, and let `f ∈ L¹(ν) ∩ L²(ν)` be a deterministic mark profile. Over a step `(a, b]`,
`0 ≤ a ≤ b`, almost surely `f` is integrable on `(a, b] × E` against `N(ω)` and the compensated
integral of `f` is the raw integral minus its compensator:

  `∫_E f(e) ΔÑ(de) = ∫_{(a, b] × E} f(e) N(ω)(ds, de) − (b − a) ∫_E f dν`.

The mean measure of `N` is its reference intensity (Campbell's formula), so the raw integral of
`|f|` over the step has mean `(b − a) ‖f‖_{L¹(ν)}`. At a simple profile the identity is the
definition of the compensated step integral. Simple functions converging to `f` both in `L¹(ν)`
and in `L²(ν)` then carry the identity to `f`: the compensated integrals converge in `L²(P)` and
the raw integrals minus their compensators converge in `L¹(P)`.

## Main statements

* `LevyStochCalc.Poisson.PoissonRandomMeasure.bind_N` — the mean measure of a Poisson random
  measure is its reference intensity.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.lintegral_lintegral_N` — Campbell's formula.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.ae_integrableOn_cell` — an integrable mark profile
  is almost surely integrable on a step times the mark space.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_integral_sub` — the compensated integral of a
  mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus its compensator.
* `LevyStochCalc.Poisson.compensatedProfileRepr_ae_eq_integral_sub` — the same for the
  representative of the compensated integral for a sub-σ-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The mean measure -/

namespace PoissonRandomMeasure

variable (N : PoissonRandomMeasure P ν)

end PoissonRandomMeasure

/-! ### Simple profiles -/


theorem _root_.Prove2MeSourceProof.h_590c988163634556081c71db (N : PoissonRandomMeasure P ν)
    (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) {b : ℝ} (hab : a ≤ b) :
    G.stepIntegral N a b =ᵐ[P] fun ω =>
      (∫ q in Set.Ioc a b ×ˢ Set.univ, G.toFun q.2 ∂(N.N ω)) - (b - a) * ∫ e, G.toFun e ∂ν := by
  have hfin : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := fun k => by
    rw [LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k)
  have hcount : ∀ᵐ ω ∂P, ∀ k, N.N ω (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [N.integer_valued (measurableSet_Ioc.prod (G.B_measurable k)) (hfin k)]
      with ω hω
    obtain ⟨n, hn⟩ := hω
    rw [hn]
    exact ENNReal.natCast_ne_top n
  filter_upwards [hcount] with ω hω
  have hW : MeasurableSet (Set.Ioc a b ×ˢ (Set.univ : Set E)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hintN : ∀ k, Integrable (fun q : ℝ × E => G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) q.2)
      ((N.N ω).restrict (Set.Ioc a b ×ˢ Set.univ)) := by
    intro k
    refine Integrable.const_mul ?_ _
    have hfun : (fun q : ℝ × E => (G.B k).indicator (fun _ => (1 : ℝ)) q.2)
        = (Prod.snd ⁻¹' G.B k).indicator fun _ => (1 : ℝ) := by
      funext q
      by_cases hq : q.2 ∈ G.B k
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' G.B k from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' G.B k from hq)]
    rw [hfun, integrable_indicator_iff (measurable_snd (G.B_measurable k))]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (measurable_snd (G.B_measurable k))]
    refine ne_top_of_le_ne_top (hω k) (measure_mono fun q hq => ?_)
    exact ⟨hq.2.1, hq.1⟩
  have hintν : ∀ k, Integrable (fun e => G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) e) ν :=
    fun k => (integrable_indicator_iff (G.B_measurable k)).2
      (integrableOn_const (G.B_finite k)) |>.const_mul _
  have hraw : ∫ q in Set.Ioc a b ×ˢ Set.univ, G.toFun q.2 ∂(N.N ω)
      = ∑ k, G.c k * (N.N ω (Set.Ioc a b ×ˢ G.B k)).toReal := by
    simp only [LevyStochCalc.Poisson.SimpleProfile.toFun]
    rw [integral_finsetSum _ fun k _ => hintN k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, setIntegral_indicator_snd _ _ (G.B_measurable k),
      measureReal_def]
  have hcomp : (b - a) * ∫ e, G.toFun e ∂ν
      = ∑ k, G.c k * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal := by
    simp only [LevyStochCalc.Poisson.SimpleProfile.toFun]
    rw [integral_finsetSum _ fun k _ => hintν k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_indicator_const _ (G.B_measurable k), smul_eq_mul, mul_one,
      LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.2 hab), measureReal_def]
    ring
  rw [hraw, hcomp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated, mul_sub]
/-! ### The pathwise identity -/

section Repr

variable {Ω' : Type u} (m : MeasurableSpace Ω') [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

end Repr

end LevyStochCalc.Poisson


