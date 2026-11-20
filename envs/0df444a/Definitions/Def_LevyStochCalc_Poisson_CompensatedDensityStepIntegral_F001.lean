-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:49:33.675954+00:00
-- url     : https://prove2.me/theorems/109eb22c-b4cd-4009-9fe8-13bda7820e19
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityStepIntegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityStepIntegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F000
import Definitions.Def_LevyStochCalc_Poisson_Filtered_F000
import Definitions.Def_SourceProof_839c3c586f330ad57afd5326
import Definitions.Def_SourceProof_b329aafcf3facb3fc4e13667
import Definitions.Def_SourceProof_bed7648bbf21e6d2454c31ed
import Definitions.Def_SourceProof_e0e24eaf49ef31dab57f4745
import Definitions.Def_SourceProof_ee220f6d1489c9eefbf823d3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Step (finite-sum) predictable integrands

The compensated integral of a finite family of simple predictable integrands, its martingale
property and square-integrability on the natural filtration, together with the covariance
identities for compensated masses of disjoint and of nested space-time sets that underlie the
`L²` isometry.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Step (finite-sum) predictable integrands

The mark-discretised approximant is rank-`>1` in the mark, so it is a finite
`ℝ`-combination of `SimplePredictable` pieces rather than a single one. Its
compensated integral is the sum of the pieces' integrals, and (being a sum of the
per-piece martingales) it is again a martingale on the natural filtration. -/

/-- A finite family of simple predictables integrates to an `L²` function at the
horizon `T` (finite sum of the per-piece `L²` integrals). -/
lemma stepIntegral_memLp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((Φ j).partition i.castSucc)) ((Φ j).ξ i)) :
    MeasureTheory.MemLp (fun ω => stepIntegral N Φ T ω) 2 P :=
  MeasureTheory.memLp_finsetSum Finset.univ
    (fun j _ => _root_.Prove2MeSourceProof.h_ee220f6d1489c9eefbf823d3 N ℱ hℱ hT (Φ j) (h_adapt j))
/-- **Disjoint compensated increments are uncorrelated.** For measurable `B, B'`
with finite reference intensity and `Disjoint B B'`, the compensated values
`Ñ(B), Ñ(B')` are independent (Poisson disjoint independence) and mean-zero, so
`E[Ñ(B)·Ñ(B')] = 0`. The bilinear building block for the step-integral isometry.
(The two-set family is indexed by `ULift (Fin 2)` to match the structure-field
universe of `independent_disjoint`.) -/
lemma compensated_cross_disjoint_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hdisj : Disjoint B B') :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P = 0 := by
  -- index the pair by `ULift (Fin 2)` (universe of `independent_disjoint`'s `ι`).
  set G : ULift (Fin 2) → Set (ℝ × E) := fun i => ![B, B'] i.down with hG
  have hmeas : ∀ i, MeasurableSet (G i) := by
    rintro ⟨i⟩; fin_cases i <;> first | exact hB | exact hB'
  have hpair : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    rintro ⟨i⟩ ⟨j⟩ hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hdisj | exact hdisj.symm
  -- `N(·,B)` and `N(·,B')` are independent.
  have hidx : ProbabilityTheory.IndepFun (fun ω => N.N ω B) (fun ω => N.N ω B') P := by
    have h01 : (ULift.up (0 : Fin 2)) ≠ ULift.up (1 : Fin 2) := by
      simp
    have h := (N.independent_disjoint G hmeas hpair).indepFun h01
    simpa [hG] using h
  -- `Ñ(B) = (·.toReal − ν̂(B).toReal) ∘ N(·,B)`, so independence is preserved.
  have hcompeq : (fun ω => N.compensated B ω)
      = (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
        ∘ (fun ω => N.N ω B) := by funext ω; rfl
  have hcompeq' : (fun ω => N.compensated B' ω)
      = (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B').toReal)
        ∘ (fun ω => N.N ω B') := by funext ω; rfl
  have hindep : ProbabilityTheory.IndepFun
      (fun ω => N.compensated B ω) (fun ω => N.compensated B' ω) P := by
    rw [hcompeq, hcompeq']
    exact hidx.comp (ENNReal.measurable_toReal.sub_const _)
      (ENNReal.measurable_toReal.sub_const _)
  have hasm : MeasureTheory.AEStronglyMeasurable (fun ω => N.compensated B ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _).aestronglyMeasurable
  have hasm' : MeasureTheory.AEStronglyMeasurable (fun ω => N.compensated B' ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB')).sub_const _).aestronglyMeasurable
  rw [hindep.integral_fun_mul_eq_mul_integral hasm hasm',
    _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed N hB hfin, zero_mul]
/-- **Second moment of a difference of disjoint compensated increments.** For
measurable disjoint `C, D` with finite intensity,
`E[(Ñ(C) − Ñ(D))²] = ν̂(C).toReal + ν̂(D).toReal` — the cross term drops out by
`compensated_cross_disjoint_zero`, the squares by `compensated_second_moment`.
This is the two-piece isometry for the disjoint-support step-integral route. -/
lemma compensated_diff_sq_disjoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {C D : Set (ℝ × E)} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤)
    (hDf : LevyStochCalc.Poisson.referenceIntensity ν D ≠ ⊤)
    (hdisj : Disjoint C D) :
    ∫ ω, (N.compensated C ω - N.compensated D ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν C).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal := by
  have hCsq := _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hC hCf
  have hDsq := _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hD hDf
  have hCD := _root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N hC hD hCf hDf
  have h2UV : MeasureTheory.Integrable
      (fun ω => 2 * (N.compensated C ω * N.compensated D ω)) P := hCD.const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => (N.compensated C ω) ^ 2 - 2 * (N.compensated C ω * N.compensated D ω)) P :=
    hCsq.sub h2UV
  have hpt : (fun ω => (N.compensated C ω - N.compensated D ω) ^ 2)
      = (fun ω => (N.compensated C ω) ^ 2
          - 2 * (N.compensated C ω * N.compensated D ω) + (N.compensated D ω) ^ 2) := by
    funext ω; ring
  rw [hpt,
    MeasureTheory.integral_add hmid hDsq,
    MeasureTheory.integral_sub hCsq h2UV,
    MeasureTheory.integral_const_mul,
    compensated_cross_disjoint_zero N hC hD hCf hdisj,
    _root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 N hC hCf, _root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 N hD hDf]
  ring
end LevyStochCalc.Poisson.Compensated


