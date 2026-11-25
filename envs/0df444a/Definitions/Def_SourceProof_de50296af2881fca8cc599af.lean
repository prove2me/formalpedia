-- Prove2me | Definitions.Def_SourceProof_de50296af2881fca8cc599af
-- name    : SourceProof_de50296af2881fca8cc599af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:57.796104+00:00
-- url     : https://prove2.me/theorems/ce2522a5-3660-4368-8b62-ca36b7b3283b
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_indicator_Ioc

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_93d83bd178e867d6847b2954

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-sum formulas for the canonical Stieltjes integral

Intervals are open on the left and closed on the right. Stopping at a finite
horizon caps both endpoints; intervals starting after the horizon contribute zero.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal BigOperators

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_de50296af2881fca8cc599af {a b : ℝ≥0} (hab : a ≤ b)
    (c : ℝ) (T : ℝ≥0) :
    pathStieltjesIncrementIntegral x hx hr ((Ioc a b).indicator (fun _ ↦ c)) 0 T =
      c * (x (min b T) - x (min a T)) := by
  have heq : Ioc 0 T ∩ Ioc a b = Ioc a (min b T) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, le_min_iff]
    exact ⟨fun ⟨⟨_, huT⟩, hua, hub⟩ ↦ ⟨hua, hub, huT⟩,
      fun ⟨hua, hub, huT⟩ ↦ ⟨⟨bot_le.trans_lt hua, huT⟩, hua, hub⟩⟩
  simp only [StochLean.pathStieltjesIncrementIntegral, setIntegral_indicator measurableSet_Ioc,
    heq, setIntegral_const, smul_eq_mul, measureReal_def]
  by_cases hTa : T ≤ a
  · rw [Ioc_eq_empty_of_le (min_le_right b T |>.trans hTa), measure_empty, measure_empty,
      ENNReal.toReal_zero, zero_mul, sub_self, min_eq_right hTa,
      min_eq_right (hTa.trans hab), sub_self, mul_zero]
  · have haT : a ≤ T := (lt_of_not_ge hTa).le
    rw [← sub_mul, _root_.Prove2MeSourceProof.h_93d83bd178e867d6847b2954 x hx hr (le_min hab haT),
      min_eq_left haT, mul_comm]
end StochLean


