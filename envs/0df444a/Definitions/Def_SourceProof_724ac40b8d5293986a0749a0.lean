-- Prove2me | Definitions.Def_SourceProof_724ac40b8d5293986a0749a0
-- name    : SourceProof_724ac40b8d5293986a0749a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:01:59.64995+00:00
-- url     : https://prove2.me/theorems/820be23b-c788-4561-83f1-fd6399e3565c
-- title:
--   LevyStochCalc source proof: LevyStochCalc.integral_abs_add_four_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First absolute moment from a second-moment bound

On a probability space the first absolute moment of a real random variable is bounded by the
square root of its second moment.

## Main statements

* `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le` — `𝔼|f| ≤ √V` whenever `𝔼f² ≤ V`.
* `LevyStochCalc.integral_abs_le_of_bounded` — `𝔼|f| ≤ K` for `|f| ≤ K`.
* `LevyStochCalc.integral_abs_add_four_le` — the triangle inequality for four summands.
-/

namespace LevyStochCalc

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_724ac40b8d5293986a0749a0 {P : Measure Ω} [IsProbabilityMeasure P]
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by
  have hab : Integrable (fun ω => |a ω| + |b ω|) P := ha.abs.add hb.abs
  have habc : Integrable (fun ω => |a ω| + |b ω| + |c ω|) P := hab.add hc.abs
  have habcd : Integrable (fun ω => |a ω| + |b ω| + |c ω| + |d ω|) P := habc.add hd.abs
  have htri : ∀ ω, |a ω + b ω + c ω + d ω| ≤ |a ω| + |b ω| + |c ω| + |d ω| := by
    intro ω
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  calc ∫ ω, |a ω + b ω + c ω + d ω| ∂P
      ≤ ∫ ω, (|a ω| + |b ω| + |c ω| + |d ω|) ∂P :=
        integral_mono (((ha.add hb).add hc).add hd).abs habcd htri
    _ = ∫ ω, (|a ω| + |b ω| + |c ω|) ∂P + ∫ ω, |d ω| ∂P := integral_add habc hd.abs
    _ = ∫ ω, (|a ω| + |b ω|) ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
        rw [integral_add hab hc.abs]
    _ = ∫ ω, |a ω| ∂P + ∫ ω, |b ω| ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
        rw [integral_add ha.abs hb.abs]
    _ ≤ A + B + C + D := add_le_add (add_le_add (add_le_add hA hB) hC) hD
end LevyStochCalc


