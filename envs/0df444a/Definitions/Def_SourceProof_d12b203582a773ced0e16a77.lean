-- Prove2me | Definitions.Def_SourceProof_d12b203582a773ced0e16a77
-- name    : SourceProof_d12b203582a773ced0e16a77
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:36:18.597786+00:00
-- url     : https://prove2.me/theorems/69582c31-f820-58d8-8d17-d4ea10c7c1ee
-- title:
--   StochLean source theorem: StochLean.integrable_pointAtomicPart_div_singleton

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
import Definitions.Def_SourceProof_e0a7184b78c69e488562dae9
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

theorem _root_.Prove2MeSourceProof.h_d12b203582a773ced0e16a77
    (hg : Measurable g) (hm : Measurable (fun t ↦ μ.real {t}))
    (hs : Summable (fun t ↦ |g t|)) :
    Integrable (fun t ↦ g t / μ.real {t}) (pointAtomicPart μ) := by
  apply _root_.Prove2MeSourceProof.h_e0a7184b78c69e488562dae9 (hg.div hm)
  apply hs.of_norm_bounded
  intro t
  simp only [Pi.div_apply]
  have hm0 : 0 ≤ μ.real {t} := ENNReal.toReal_nonneg
  by_cases hz : μ.real {t} = 0
  · simp [hz, abs_nonneg]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0, Real.norm_eq_abs,
      abs_abs, abs_div, abs_of_nonneg hm0]
    exact (mul_div_cancel₀ |g t| hz).le
end StochLean


