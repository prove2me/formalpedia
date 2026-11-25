-- Prove2me | Definitions.Def_SourceProof_d0a4df1f377b948070a9df01
-- name    : SourceProof_d0a4df1f377b948070a9df01
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:49.208126+00:00
-- url     : https://prove2.me/theorems/262c3c62-157f-5939-bbae-70ab21753572
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIntegral_sub

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_0e9a3c1ecba0183e8cff41a4
import Definitions.Def_SourceProof_17e97db7cf70e0ac4580327f
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

theorem _root_.Prove2MeSourceProof.h_d0a4df1f377b948070a9df01
    (hf : IntegrableOn f (Ioc 0 t) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 t) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIntegral x hx hr (fun u ↦ f u - g u) t =
      pathStieltjesIntegral x hx hr f t - pathStieltjesIntegral x hx hr g t := by
  simp only [StochLean.pathStieltjesIntegral, StochLean.pathStieltjesIncrementIntegral,
    integral_sub (_root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f hf)
      (_root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f hg),
    integral_sub (_root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 hf)
      (_root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 hg)]
  ring
end StochLean


