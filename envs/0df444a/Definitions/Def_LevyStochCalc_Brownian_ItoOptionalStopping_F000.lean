-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
-- name    : LevyStochCalc_Brownian_ItoOptionalStopping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:01:26.448434+00:00
-- url     : https://prove2.me/theorems/e5e74dc2-b6d6-48ac-bb3f-6ec3ac10e558
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoOptionalStopping
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoOptionalStopping. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFinsetSum_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000
import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F002
import Definitions.Def_SourceProof_4014cddbf3dd1c22757fef9e
import Definitions.Def_SourceProof_a85377d9ae43b1c0795fd7b5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Optional stopping for the Itô integral, for a stopping time of finite range

Cutting the integrand off at a stopping time that takes finitely many values below the horizon
subtracts, for each of those values `c`, the increment of the integral across `(c, T]` weighted
by the event `{τ = c}`. That weight is known at `c` and the cut integrand is carried by `(c, T]`,
so it passes inside the integral; the resulting sum telescopes into the integral evaluated at
`τ ∧ T`.

## Main statements

* `LevyStochCalc.Brownian.Ito.hitInd`, `cutTerm` — the weight and the cut integrand.
* `LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum` — the pathwise decomposition of the cut
  integrand.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped` — the identity.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Square-integrability transfers along a pointwise domination of the integrands. -/
theorem energy_lt_top_of_abs_le {K G : Ω → ℝ → ℝ} (h : ∀ ω s, |K ω s| ≤ |G ω s|)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => ?_) (hq T hT)
  have hle : (‖K ω s‖₊ : ℝ≥0∞) ≤ (‖G ω s‖₊ : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using h ω s
  gcongr
section Stopped

variable (τ : Ω → WithTop ℝ)

/-- The indicator of the event that the stopping time takes the value `c`. -/
noncomputable def hitInd (c : ℝ) : Ω → ℝ :=
  Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} fun _ => (1 : ℝ)
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem abs_hitInd_le_one (c : ℝ) (ω : Ω) : |hitInd τ c ω| ≤ 1 := by
  by_cases h : ω ∈ {ω | τ ω = ((c : ℝ) : WithTop ℝ)} <;> simp [hitInd, h]
theorem measurable_hitInd {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) : Measurable (hitInd τ c) :=
  measurable_const.indicator (ℱ.le c _ (hτ.measurableSet_eq c))
theorem stronglyMeasurable_hitInd {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ c) (hitInd τ c) := by
  letI : MeasurableSpace Ω := ℱ c
  exact (measurable_const.indicator (hτ.measurableSet_eq c)).stronglyMeasurable
/-- The part of the integrand that the cut at `τ = c` removes from the window `(c, t]`. -/
noncomputable def cutTerm (H : Ω → ℝ → ℝ) (c t : ℝ) : Ω → ℝ → ℝ :=
  fun ω s => hitInd τ c ω * indIoc Ω c t ω s * H ω s
theorem measurable_cutTerm {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (c t : ℝ) :
    Measurable (Function.uncurry (cutTerm τ H c t)) := by
  have hind : Measurable fun p : Ω × ℝ => indIoc Ω c t p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  exact (((measurable_hitInd τ hτ c).comp measurable_fst).mul hind).mul hm
theorem progressivelyMeasurable_cutTerm (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hp : Probability.ProgressivelyMeasurable ℱ H) {c t : ℝ} (hc : 0 ≤ c) (hct : c < t) :
    Probability.ProgressivelyMeasurable ℱ (cutTerm τ H c t) :=
  (_root_.Prove2MeSourceProof.h_a85377d9ae43b1c0795fd7b5 ℱ hc hct ⟨1, abs_hitInd_le_one τ c⟩
    (measurable_hitInd τ hτ c) (stronglyMeasurable_hitInd τ hτ c)).mul hp
omit [IsProbabilityMeasure P] in
theorem abs_cutTerm_le {H : Ω → ℝ → ℝ} (c t : ℝ) (ω : Ω) (s : ℝ) :
    |cutTerm τ H c t ω s| ≤ |H ω s| := by
  have h1 : |hitInd τ c ω| ≤ 1 := abs_hitInd_le_one τ c ω
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |cutTerm τ H c t ω s| = |hitInd τ c ω| * |indIoc Ω c t ω s| * |H ω s| := by
        rw [cutTerm, abs_mul, abs_mul]
    _ ≤ 1 * 1 * |H ω s| := by
        gcongr
    _ = |H ω s| := by ring
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem abs_stopped_le' {H : Ω → ℝ → ℝ} (ω : Ω) (s : ℝ) :
    |Probability.stopped τ H ω s| ≤ |H ω s| := Probability.abs_stopped_le τ H ω s
/-- The integrand restricted to a window, as a `cutTerm` with unit weight. -/
noncomputable def indTerm (H : Ω → ℝ → ℝ) (c t : ℝ) : Ω → ℝ → ℝ :=
  fun ω s => indIoc Ω c t ω s * H ω s
omit [IsProbabilityMeasure P] in
theorem measurable_indTerm {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) (c t : ℝ) :
    Measurable (Function.uncurry (indTerm H c t)) := by
  have hind : Measurable fun p : Ω × ℝ => indIoc Ω c t p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  exact hind.mul hm
theorem progressivelyMeasurable_indTerm (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) {c t : ℝ} (hc : 0 ≤ c)
    (hct : c < t) : Probability.ProgressivelyMeasurable ℱ (indTerm H c t) := by
  have hfun : (fun (ω : Ω) (s : ℝ) => (1 : ℝ) * indIoc Ω c t ω s)
      = fun ω s => indIoc Ω c t ω s := by
    funext ω s
    ring
  have h1 := _root_.Prove2MeSourceProof.h_a85377d9ae43b1c0795fd7b5 (Ω := Ω) ℱ hc hct
    (V := fun _ => (1 : ℝ)) ⟨1, fun ω => by simp⟩ measurable_const stronglyMeasurable_const
  exact (hfun ▸ h1).mul hp
omit [IsProbabilityMeasure P] in
theorem abs_indTerm_le {H : Ω → ℝ → ℝ} (c t : ℝ) (ω : Ω) (s : ℝ) :
    |indTerm H c t ω s| ≤ |H ω s| := by
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |indTerm H c t ω s| = |indIoc Ω c t ω s| * |H ω s| := by rw [indTerm, abs_mul]
    _ ≤ 1 * |H ω s| := by gcongr
    _ = |H ω s| := by ring
section Identity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Identity

end Stopped

end LevyStochCalc.Brownian.Ito


