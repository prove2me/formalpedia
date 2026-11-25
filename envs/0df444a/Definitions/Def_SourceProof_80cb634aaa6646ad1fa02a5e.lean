-- Prove2me | Definitions.Def_SourceProof_80cb634aaa6646ad1fa02a5e
-- name    : SourceProof_80cb634aaa6646ad1fa02a5e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:09:48.230668+00:00
-- url     : https://prove2.me/theorems/381f327e-8149-4efd-8c12-67e43e3cd72c
-- title:
--   StochLean source theorem: StochLean.square_sub_twice_leftIntegral_eq_jumpIntegral

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_70df86d6eada83093c0971aa
import Definitions.Def_SourceProof_a62252018268fa29cedecd73
import Definitions.Def_SourceProof_ca371899a004561914a59371
import Definitions.Def_SourceProof_f0d7366f281cd44e7eb0e371

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The self-integral identity for a cadlag FV path

Finite-cell algebra and genuine left/right endpoint convergence prove the
identity, including the full contribution of jumps and the initial square.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_80cb634aaa6646ad1fa02a5e {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hc : IsCadlagPath x) (T : ℝ≥0) :
    x T ^ 2 - 2 * pathStieltjesIncrementIntegral x hv hc.1 (Function.leftLim x) 0 T =
      x 0 ^ 2 + pathStieltjesIncrementIntegral x hv hc.1
        (fun u ↦ x u - Function.leftLim x u) 0 T := by
  let π : ℕ → StochLean.TimePartition T := fun n ↦ (StochLean.LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      ((_root_.Prove2MeSourceProof.h_f0d7366f281cd44e7eb0e371 _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4) (fun _ ↦ T))
  have hl := _root_.Prove2MeSourceProof.h_a62252018268fa29cedecd73 (hx := hv) (hr := hc.1) hc hm
  have hs : Tendsto (fun n ↦ StochLean.quadraticVariationSum (π n) x) atTop
      (𝓝 (x T ^ 2 - x 0 ^ 2 -
        2 * StochLean.pathStieltjesIncrementIntegral x hv hc.1 (Function.leftLim x) 0 T)) := by
    simpa only [_root_.Prove2MeSourceProof.h_ca371899a004561914a59371] using
      (tendsto_const_nhds (x := x T ^ 2 - x 0 ^ 2)).sub (hl.const_mul 2)
  have he := tendsto_nhds_unique hs
    (_root_.Prove2MeSourceProof.h_70df86d6eada83093c0971aa hv hc hm)
  linarith
end StochLean


