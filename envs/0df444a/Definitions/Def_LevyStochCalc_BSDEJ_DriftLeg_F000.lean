-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F000
-- name    : LevyStochCalc_BSDEJ_DriftLeg_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:17:57.869886+00:00
-- url     : https://prove2.me/theorems/745a0e52-b987-483a-8f50-0a86d265d041
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.DriftLeg
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.DriftLeg. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
import Mathlib.MeasureTheory.Integral.SetToL1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The drift leg of a Picard iterate

For a drift `b : Ω → ℝ → ℝ` of finite energy on the horizon `[0, T]` and vanishing off it, the
drift leg is the primitive `t ↦ ∫_{[0, t]} b ω s ds`, restricted to the sample points on which
`b ω` is integrable over `[0, T]` and set to `0` elsewhere. That restriction is a `P`-conull set,
so the drift leg is a version of the raw primitive, and on it every path is the primitive of a
globally integrable function, hence continuous.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.integrablePaths` — the sample points whose drift path is integrable
  over the horizon.
* `LevyStochCalc.BSDEJ.Solves.driftLeg` — the primitive of the drift, cut to those sample points.

## Main statements

* `driftLeg_ae_eq` — the drift leg is a version of the raw primitive.
* `setIntegral_Icc_eq_intervalIntegral` — the integral over `[0, t]` is the interval integral
  from `0` to `t`, for every real `t`.
* `continuous_driftLeg` — every path of the drift leg is continuous.
* `stronglyAdapted_driftLeg`, `adapted_driftLeg` — the drift leg is adapted to the filtration of
  the drift.
* `adapted_driftLeg_of_rightCont` — the drift leg is adapted to the filtration already when the
  drift is progressive for the right-continuous filtration.
* `measurable_uncurry_driftLeg` — the drift leg is jointly measurable in time and sample point.
* `driftLeg_sub_ae` — the drift leg at the horizon splits at an intermediate time.
* `lintegral_biSup_sq_driftLeg_lt_top` — the drift leg has finite `S²` seminorm.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### The paths on which the drift is integrable -/

/-- The set of sample points whose drift path is integrable over the horizon `[0, T]`. -/
def integrablePaths (b : Ω → ℝ → ℝ) (T : ℝ) : Set Ω :=
  {ω | IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume}
/-- The set of sample points with an integrable drift path is measurable. -/
theorem measurableSet_integrablePaths (hbm : Measurable (Function.uncurry b)) :
    MeasurableSet (integrablePaths b T) :=
  measurableSet_integrable (μ := volume.restrict (Set.Icc (0 : ℝ) T)) hbm.stronglyMeasurable
/-- The extended norm of a square is the square of the extended norm. -/
private theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl
/-- A function with finite energy on a bounded window is square integrable there. -/
private theorem memLp_two_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {c : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) c, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) c)) := by
  refine (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => enorm_sq_eq (f s))) hfin
/-- A function with finite energy on a bounded window is integrable there. -/
private theorem integrableOn_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {c : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) c, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    IntegrableOn f (Set.Icc (0 : ℝ) c) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) c)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  exact (memLp_two_of_lintegral_sq_lt_top hf hfin).integrable (by norm_num)
/-- A drift of finite energy on the horizon has an integrable path at almost every sample
point. -/
theorem ae_mem_integrablePaths (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) : ∀ᵐ ω ∂P, ω ∈ integrablePaths b T := by
  have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hbm.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hae : ∀ᵐ ω ∂P, (∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤ :=
    ae_lt_top hmeas hbq
  filter_upwards [hae] with ω hω
  exact integrableOn_of_lintegral_sq_lt_top (hbm.comp (measurable_const.prodMk measurable_id)) hω
/-! ### The drift leg -/

/-- The primitive `t ↦ ∫_{[0, t]} b ω s ds` of the drift, cut to the sample points on which the
drift is integrable over the horizon. -/
noncomputable def driftLeg (b : Ω → ℝ → ℝ) (T : ℝ) : ℝ → Ω → ℝ := fun t =>
  (integrablePaths b T).indicator fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s
/-- On a sample point with an integrable drift path the drift leg is the primitive. -/
theorem driftLeg_of_mem {ω : Ω} (hω : ω ∈ integrablePaths b T) (t : ℝ) :
    driftLeg b T t ω = ∫ s in Set.Icc (0 : ℝ) t, b ω s :=
  Set.indicator_of_mem hω _
/-- Off the sample points with an integrable drift path the drift leg vanishes. -/
theorem driftLeg_of_notMem {ω : Ω} (hω : ω ∉ integrablePaths b T) (t : ℝ) :
    driftLeg b T t ω = 0 :=
  Set.indicator_of_notMem hω _
/-- The drift leg is a version of the primitive of the drift. -/
theorem driftLeg_ae_eq (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (t : ℝ) :
    driftLeg b T t =ᵐ[P] fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s := by
  filter_upwards [ae_mem_integrablePaths hbm hbq] with ω hω
  exact driftLeg_of_mem hω t
/-- For a drift vanishing off the horizon the integral over `[0, t]` is the interval integral
from `0` to `t`, at every real time. -/
theorem setIntegral_Icc_eq_intervalIntegral (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (ω : Ω) (t : ℝ) : ∫ s in Set.Icc (0 : ℝ) t, b ω s = ∫ s in (0 : ℝ)..t, b ω s := by
  rcases le_or_gt 0 t with ht | ht
  · rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  · have h0 : Set.EqOn (b ω) (fun _ => (0 : ℝ)) (Set.Ioo t (0 : ℝ)) := fun s hs =>
      hbz ω s fun hc => absurd hc.1 (not_le.mpr hs.2)
    have hIoo : ∫ s in Set.Ioo t (0 : ℝ), b ω s = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo h0]
      simp
    rw [Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty,
      intervalIntegral.integral_of_ge ht.le, integral_Ioc_eq_integral_Ioo, hIoo, neg_zero]
end LevyStochCalc.BSDEJ.Solves


