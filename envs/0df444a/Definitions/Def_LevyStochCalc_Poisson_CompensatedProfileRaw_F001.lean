-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRaw_F001
-- name    : LevyStochCalc_Poisson_CompensatedProfileRaw_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:03:17.653252+00:00
-- url     : https://prove2.me/theorems/910c0924-1f2a-4902-a042-77108d011a88
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfileRaw
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfileRaw. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileRaw_F000
import Definitions.Def_SourceProof_79fc0dfc208a12c994833c8a

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

/-! ### The pathwise identity -/

/-- **The compensated integral of a mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus
its compensator.** Almost surely the profile is integrable on `(a, b] × E` against the Poisson
random measure and `∫_E f ΔÑ = ∫_{(a, b] × E} f(e) N(ds, de) − (b − a) ∫_E f dν`. -/
theorem compensatedProfile_ae_eq_integral_sub (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf1 : Integrable f ν) (hf2 : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω)
      ∧ compensatedProfile N f a b ω
        = (∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) - (b - a) * ∫ e, f e ∂ν := by
  set f' := hf1.1.mk f
  have hmk : f =ᵐ[ν] f' := hf1.1.ae_eq_mk
  have hfm : Measurable f' := hf1.1.stronglyMeasurable_mk.measurable
  filter_upwards [N.ae_integrableOn_cell hf1 ha b, N.ae_ae_eq_comp_snd hmk,
    _root_.Prove2MeSourceProof.h_79fc0dfc208a12c994833c8a N hfm (hf1.congr hmk)
      (hf2.ae_eq hmk) ha hab] with ω hint hωe hω
  refine ⟨hint, ?_⟩
  rw [compensatedProfile_congr_ae N hmk a b, hω, integral_congr_ae hmk,
    integral_congr_ae (ae_restrict_of_ae hωe)]
section Repr

variable {Ω' : Type u} (m : MeasurableSpace Ω') [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

/-- The representative of the compensated integral of a mark profile in `L¹(ν) ∩ L²(ν)` for a
sub-σ-algebra is the raw integral minus its compensator. -/
theorem compensatedProfileRepr_ae_eq_integral_sub (N : PoissonRandomMeasure P' ν) {f : E → ℝ}
    (hf1 : Integrable f ν) (hf2 : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P', IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω)
      ∧ compensatedProfileRepr m N f a b ω
        = (∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) - (b - a) * ∫ e, f e ∂ν := by
  filter_upwards [compensatedProfile_ae_eq_integral_sub N hf1 hf2 ha hab,
    compensatedProfileRepr_ae_eq m N f a b] with ω hω hr
  exact ⟨hω.1, hr.trans hω.2⟩
end Repr

end LevyStochCalc.Poisson


