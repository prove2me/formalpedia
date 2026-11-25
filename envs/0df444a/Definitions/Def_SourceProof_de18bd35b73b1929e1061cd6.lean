-- Prove2me | Definitions.Def_SourceProof_de18bd35b73b1929e1061cd6
-- name    : SourceProof_de18bd35b73b1929e1061cd6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:57.231111+00:00
-- url     : https://prove2.me/theorems/a48483f0-ecc4-4391-aeab-8cc0420eca4e
-- title:
--   StochLean source theorem: StochLean.norm_pathStieltjesIntegral_le

import Definitions.Def_SourceProof_819cd4efcc2d1f6e4f6ed736
import Definitions.Def_SourceProof_82b057b5fc05c115d43ef115

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-horizon integration against a locally BV path

The increment integral on `(s,t]` is the difference of integrals against the
canonical positive and negative Stieltjes components. Integrability is measured
against their sum, the total-variation measure. The source integral from time
zero additionally contains `f 0 * x 0`; this is not a measure atom.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

variable (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_de18bd35b73b1929e1061cd6 {C : ℝ} (hC : ∀ u ∈ Icc 0 t, ‖f u‖ ≤ C) :
    ‖pathStieltjesIntegral x hx hr f t‖ ≤ C * (|x 0| + pathTotalVariation x t) := by
  have h0 := hC 0 ⟨le_rfl, bot_le⟩
  have hinc := _root_.Prove2MeSourceProof.h_819cd4efcc2d1f6e4f6ed736
    (x := x) (hx := hx) (hr := hr) (fun u hu ↦ hC u ⟨hu.1.le, hu.2⟩) bot_le
  calc
    ‖StochLean.pathStieltjesIntegral x hx hr f t‖ ≤
        ‖f 0 * x 0‖ + ‖StochLean.pathStieltjesIncrementIntegral x hx hr f 0 t‖ := norm_add_le _ _
    _ ≤ C * |x 0| + C * (eVariationOn x (Icc 0 t)).toReal :=
      add_le_add (by simpa only [norm_mul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right h0 (norm_nonneg (x 0))) hinc
    _ = _ := by rw [_root_.Prove2MeSourceProof.h_82b057b5fc05c115d43ef115, mul_add]
end StochLean


