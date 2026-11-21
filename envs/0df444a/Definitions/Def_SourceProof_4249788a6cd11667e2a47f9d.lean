-- Prove2me | Definitions.Def_SourceProof_4249788a6cd11667e2a47f9d
-- name    : SourceProof_4249788a6cd11667e2a47f9d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:43.35396+00:00
-- url     : https://prove2.me/theorems/6eea266e-1116-4970-9bcb-130370e1dc6b
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stopOf_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_4249788a6cd11667e2a47f9d {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ)) (hZm : Measurable (Function.uncurry Z)) (hT : 0 ≤ T)
    (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by
  have hZi : ∀ i : Fin n, Measurable fun p : Ω × ℝ => Z (min p.2 T) p.1 i := fun i =>
    (measurable_pi_apply i).comp
      (hZm.comp ((measurable_snd.min measurable_const).prodMk measurable_fst))
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      (ENNReal.continuous_coe.measurable.comp (hZi i).nnnorm).pow_const 2
  rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T'))
    (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
  calc ∫⁻ s in Set.Icc (0 : ℝ) T',
        (∫⁻ ω, ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T',
          (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) ∂volume :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc
          (fun s hs => LevyStochCalc.Ito.Picard.lintegral_sq_le_bieleckiNorm_sq_raw Z ⟨le_min hs.1 hT, min_le_right s T⟩)
    _ = (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) * volume (Set.Icc (0 : ℝ) T') :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal T' * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by
        rw [Real.volume_Icc, sub_zero, mul_comm]
namespace SBoundedProcess

end SBoundedProcess

end LevyStochCalc.Ito.Picard


