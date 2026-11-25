-- Prove2me | Definitions.Def_SourceProof_e0a7184b78c69e488562dae9
-- name    : SourceProof_e0a7184b78c69e488562dae9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:11.821413+00:00
-- url     : https://prove2.me/theorems/58edf9be-e22e-5d44-b8df-353313a94a71
-- title:
--   StochLean source theorem: StochLean.integrable_pointAtomicPart_of_summable

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
import Definitions.Def_SourceProof_fc5f89aed67e82971b1326cd
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrability from actual summable point-atomic weights

The finite measure may live on an uncountable space. Only its intrinsic
countable atom set is used. The inverse singleton mass converts supported
unweighted series into integrals, with zero-mass points handled explicitly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
  {μ : Measure T} [IsFiniteMeasure μ] {f g : T → ℝ}

theorem _root_.Prove2MeSourceProof.h_e0a7184b78c69e488562dae9
    (hf : Measurable f) (hs : Summable (fun t ↦ μ.real {t} * ‖f t‖)) :
    Integrable f (pointAtomicPart μ) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, StochLean.pointAtomicPart, lintegral_countable _ (_root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd μ)]
  have he (t : StochLean.pointAtomSet μ) : ‖f t‖ₑ * μ {(t : T)} =
      ENNReal.ofReal (μ.real {(t : T)} * ‖f t‖) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_toReal (measure_ne_top μ {(t : T)}),
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    exact mul_comm _ _
  simp only [he]
  exact (hs.subtype (StochLean.pointAtomSet μ)).tsum_ofReal_lt_top
end StochLean


