-- Prove2me | Definitions.Def_SourceProof_edcd15c8d7818a605e0602ee
-- name    : SourceProof_edcd15c8d7818a605e0602ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:42:07.618934+00:00
-- url     : https://prove2.me/theorems/36df4ae3-42c2-4b2c-88bd-3b45047f3aef
-- title:
--   StochLean source theorem: StochLean.norm_pathStieltjesIntegral_sub_le

import Definitions.Def_SourceProof_7d2787f4ad27ed704ba3ff83
import Definitions.Def_SourceProof_d0a4df1f377b948070a9df01
import Definitions.Def_SourceProof_de18bd35b73b1929e1061cd6
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform continuity of finite-horizon Stieltjes integration

The pathwise operator bound includes the initial value. Local uniform convergence
therefore passes through the integral uniformly in its terminal time.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f g : ℝ≥0 → ℝ} {T t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_edcd15c8d7818a605e0602ee
    (hf : IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ u ∈ Icc 0 T, ‖f u - g u‖ ≤ C) (ht : t ≤ T) :
    ‖pathStieltjesIntegral x hx hr f t - pathStieltjesIntegral x hx hr g t‖ ≤
      C * (|x 0| + pathTotalVariation x T) := by
  have hsub : Ioc 0 t ⊆ Ioc 0 T := fun _ hu ↦ ⟨hu.1, hu.2.trans ht⟩
  rw [← _root_.Prove2MeSourceProof.h_d0a4df1f377b948070a9df01 (hf.mono_set hsub) (hg.mono_set hsub)]
  exact (_root_.Prove2MeSourceProof.h_de18bd35b73b1929e1061cd6 (fun u hu ↦ hfg u ⟨hu.1, hu.2.trans ht⟩)).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (_root_.Prove2MeSourceProof.h_7d2787f4ad27ed704ba3ff83 hx ht)) hC)
end StochLean


