-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F001
-- name    : LevyStochCalc_Brownian_VectorItoStopped_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:44:17.476735+00:00
-- url     : https://prove2.me/theorems/741edf9a-2e10-44a7-ac9a-20a7a7a88907
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoStopped
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoStopped. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F000
import Definitions.Def_SourceProof_824bcd558fff0b7dee883334
import Definitions.Def_SourceProof_e0bce38e6a65980ddb5abfb5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

theorem clipTime_nonneg (ht : 0 ≤ t) (hτ0 : ((0 : ℝ) : WithTop ℝ) ≤ τ ω) :
    0 ≤ clipTime τ t ω := (_root_.Prove2MeSourceProof.h_824bcd558fff0b7dee883334 ht).mp hτ0
theorem continuous_clipTime (τ : Ω → WithTop ℝ) (ω : Ω) :
    Continuous fun t : ℝ => clipTime τ t ω := by
  by_cases hne : τ ω = ⊤
  · exact continuous_id.congr fun t => (clipTime_eq_self_of_top hne).symm
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    exact (continuous_id.min continuous_const).congr fun t => (clipTime_eq_min hr.symm).symm
end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

include hℱ in
/-- **The Itô integral of a stopped integrand is the integral evaluated at the clipped
horizon.** -/
theorem stochasticIntegralBrownian_stopped_clip
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
        (Probability.measurable_uncurry_stopped hτ hm)
        (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp)
        (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (clipTime τ t ω) ω := by
  classical
  filter_upwards [_root_.Prove2MeSourceProof.h_e0bce38e6a65980ddb5abfb5 τ W ℱ hℱ hτ hm hp hq ht J hJ0 hJt hτJ]
    with ω hω
  rw [hω]
  rcases hτJ ω with ⟨c, hcJ, hceq⟩ | hle
  · have hct : c < t := hJt c hcJ
    have hsum : ∑ c' ∈ J, hitInd τ c' ω *
        (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c' ω)
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω := by
      refine (Finset.sum_eq_single c ?_ ?_).trans ?_
      · intro c' _ hne
        have : hitInd τ c' ω = 0 := by
          refine Set.indicator_of_notMem ?_ _
          intro hmem
          exact hne (by exact_mod_cast (hmem.symm.trans hceq))
        rw [this, zero_mul]
      · intro hcon
        exact absurd hcJ hcon
      · have hone : hitInd τ c ω = 1 := by
          simp only [hitInd]
          exact Set.indicator_of_mem (by simpa using hceq) _
        rw [hone, one_mul]
    rw [hsum, clipTime_eq_min hceq, min_eq_right hct.le]
    ring
  · have hsum : ∑ c' ∈ J, hitInd τ c' ω *
        (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c' ω) = 0 := by
      refine Finset.sum_eq_zero fun c' hc' => ?_
      have : hitInd τ c' ω = 0 := by
        refine Set.indicator_of_notMem ?_ _
        intro hmem
        have : ((t : ℝ) : WithTop ℝ) ≤ ((c' : ℝ) : WithTop ℝ) := hmem ▸ hle
        exact absurd (by exact_mod_cast this) (not_le.mpr (hJt c' hc'))
      rw [this, zero_mul]
    rw [hsum, clipTime_of_le hle, sub_zero]
end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

/-- The window integral of a stopped integrand is the integral over the clipped window. -/
theorem setIntegral_stopped_eq (τ : Ω → WithTop ℝ) (b : Ω → ℝ → ℝ) {t : ℝ} (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) t, Probability.stopped τ b ω s ∂volume
      = ∫ s in Set.Icc (0 : ℝ) (clipTime τ t ω), b ω s ∂volume := by
  have hsub : Set.Icc (0 : ℝ) (clipTime τ t ω) ⊆ Set.Icc (0 : ℝ) t :=
    Set.Icc_subset_Icc le_rfl (clipTime_le_self τ t ω)
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, Probability.stopped τ b ω s
      = Set.indicator (Set.Icc (0 : ℝ) (clipTime τ t ω)) (b ω) s := by
    intro s hs
    simp only [Probability.stopped]
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · have hsc : s ≤ clipTime τ t ω := (_root_.Prove2MeSourceProof.h_824bcd558fff0b7dee883334 hs.2).mp hle
      have hmem : s ∈ Set.Icc (0 : ℝ) (clipTime τ t ω) := ⟨hs.1, hsc⟩
      rw [if_pos hle, Set.indicator_of_mem hmem]
    · have hsc : ¬ s ≤ clipTime τ t ω := fun hcon => hle ((_root_.Prove2MeSourceProof.h_824bcd558fff0b7dee883334 hs.2).mpr hcon)
      rw [if_neg hle, Set.indicator_of_notMem (fun hmem => hsc hmem.2)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_self_of_subset_right hsub]
end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

end StoppedVersion

end LevyStochCalc.Brownian.Ito


