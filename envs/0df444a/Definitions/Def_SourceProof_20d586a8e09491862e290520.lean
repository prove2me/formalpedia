-- Prove2me | Definitions.Def_SourceProof_20d586a8e09491862e290520
-- name    : SourceProof_20d586a8e09491862e290520
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:19:08.941178+00:00
-- url     : https://prove2.me/theorems/f04feb6c-e3a2-48b4-a6b0-bf495963a863
-- title:
--   LevyStochCalc source module: SourceProof_20d586a8e09491862e290520
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.memLp_two_running` comes from the `LevyStochCalc.Ito.SecondMomentToolkit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F002
import Definitions.Def_SourceProof_190a5767e8f1b936b4a6a09f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}


theorem _root_.Prove2MeSourceProof.h_20d586a8e09491862e290520 (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (running b T) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hR := LevyStochCalc.Ito.SecondMoment.stronglyMeasurable_running (T := T) hbm
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hR.aestronglyMeasurable ?_
  rw [lintegral_prod_symm _ (hR.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable]
  set K : ℝ≥0∞ := ENNReal.ofReal T
    * ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hK
  have hKlt : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbq
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, (‖LevyStochCalc.Ito.SecondMoment.running b T (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ K := by
    intro s hs
    have h1 : ∀ ω, LevyStochCalc.Ito.SecondMoment.running b T (ω, s) = ∫ r in Set.Icc (0 : ℝ) s, b r ω :=
      fun ω => LevyStochCalc.Ito.SecondMoment.running_eq hs
    simp_rw [h1]
    have hwin : ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) s, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
      lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl hs.2)
    calc ∫⁻ ω, (‖∫ r in Set.Icc (0 : ℝ) s, b r ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal s
          * ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) s, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          _root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f (f := fun ω r => b r ω) hbm hs.1
            (lt_of_le_of_lt hwin hbq)
      _ ≤ K := by
          rw [hK]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hs.2) hwin
  calc ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖LevyStochCalc.Ito.SecondMoment.running b T (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂P ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, K ∂volume :=
        setLIntegral_mono' measurableSet_Icc fun s hs => hbound s hs
    _ = K * ENNReal.ofReal T := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
    _ < ⊤ := ENNReal.mul_lt_top hKlt ENNReal.ofReal_lt_top
end Running

section Polarised

end Polarised

section PolarisedDrift

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment


