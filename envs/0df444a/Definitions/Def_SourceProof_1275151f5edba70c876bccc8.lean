-- Prove2me | Definitions.Def_SourceProof_1275151f5edba70c876bccc8
-- name    : SourceProof_1275151f5edba70c876bccc8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:10.949902+00:00
-- url     : https://prove2.me/theorems/a153af6b-f73e-4a7f-9925-ad68fac540a2
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_jump_eq_tsum

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_0d8cf2b9b86d91c4d2898be2
import Definitions.Def_SourceProof_0e9a3c1ecba0183e8cff41a4
import Definitions.Def_SourceProof_17e97db7cf70e0ac4580327f
import Definitions.Def_SourceProof_82c6d1dbda060237d4fd2c23
import Definitions.Def_SourceProof_d853fc6b74b1edd2bebb09da
import Definitions.Def_SourceProof_d9123ca2840c05f7ecf3036a
import Definitions.Def_SourceProof_ee229f4bc26677ae1664bbd3
import Definitions.Def_SourceProof_fb1f33a9464fc2436dc87cdd
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The Stieltjes integral of FV jumps is their squared-jump series

Both Jordan component integrals and both series are genuinely integrable and
summable. The real-valued `tsum` is not used to conceal a divergent series.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_1275151f5edba70c876bccc8 {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0) :
    pathStieltjesIncrementIntegral x hv hr (fun u ↦ x u - leftLim x u) 0 T =
      ∑' u : Ioc 0 T, (x u - leftLim x u) ^ 2 := by
  let p := StochLean.positiveVariationStieltjes x hv hr
  let n := StochLean.negativeVariationStieltjes x hv hr
  let j := fun u ↦ x u - leftLim x u
  have hi := _root_.Prove2MeSourceProof.h_d9123ca2840c05f7ecf3036a hv hr T
  have hc := _root_.Prove2MeSourceProof.h_82c6d1dbda060237d4fd2c23 hv hr
  have hb : ∀ t ∈ Ioc 0 T, |j t| ≤ ∑' u : Ioc 0 T, |j u| := fun t ht ↦
    _root_.Prove2MeSourceProof.h_ee229f4bc26677ae1664bbd3 hv hr T ⟨t, ht⟩
  have hp := _root_.Prove2MeSourceProof.h_d853fc6b74b1edd2bebb09da p T hb
  have hn := _root_.Prove2MeSourceProof.h_d853fc6b74b1edd2bebb09da n T hb
  change (∫ u in Ioc 0 T, j u ∂p.measure) - (∫ u in Ioc 0 T, j u ∂n.measure) = _
  rw [_root_.Prove2MeSourceProof.h_0d8cf2b9b86d91c4d2898be2 hc measurableSet_Ioc
      (_root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f hi),
    _root_.Prove2MeSourceProof.h_0d8cf2b9b86d91c4d2898be2 hc measurableSet_Ioc
      (_root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 hi), ← hp.tsum_sub hn]
  apply tsum_congr
  intro t
  rw [← sub_mul]
  change ((p.measure {(t : ℝ≥0)}).toReal - (n.measure {(t : ℝ≥0)}).toReal) * j t = _
  rw [_root_.Prove2MeSourceProof.h_fb1f33a9464fc2436dc87cdd (hx := hv) (hr := hr) t.2.1]
  exact (pow_two _).symm
end StochLean


