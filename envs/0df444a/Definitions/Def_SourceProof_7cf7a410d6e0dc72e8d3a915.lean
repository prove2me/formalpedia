-- Prove2me | Definitions.Def_SourceProof_7cf7a410d6e0dc72e8d3a915
-- name    : SourceProof_7cf7a410d6e0dc72e8d3a915
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:43:11.718375+00:00
-- url     : https://prove2.me/theorems/1d3aa90d-c9d9-53ce-bbc3-875fde1dcd3c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasFiniteVariationPaths_quadraticCovariation

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_798d59aac4a0874192da8eb2
import Definitions.Def_SourceProof_81d5b0d969fd9cee9a11b8b9

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw quadratic covariation by polarization of the canonical square bracket

This is the design's sole mixed bracket owner. It retains `X₀ Y₀`, is adapted
and cadlag, and has locally finite-variation paths. It is not asserted to be
increasing and is not a predictable compensator bracket.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_7cf7a410d6e0dc72e8d3a915
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.quadraticCovariation hY hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) hF,
    (_root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9 hX) hF, (_root_.Prove2MeSourceProof.h_81d5b0d969fd9cee9a11b8b9 hY) hF]
    with ω hsum hx hy
  have hhalf {f : ℝ≥0 → ℝ} (hf : Monotone f) : Monotone (fun t ↦ (1 / 2 : ℝ) * f t) :=
    fun _ _ hst ↦ mul_le_mul_of_nonneg_left (hf hst) (by norm_num)
  have hv := _root_.Prove2MeSourceProof.h_798d59aac4a0874192da8eb2
    (_root_.Prove2MeSourceProof.h_798d59aac4a0874192da8eb2
      ((hhalf hsum).monotoneOn univ).locallyBoundedVariationOn
      ((hhalf hx).monotoneOn univ).locallyBoundedVariationOn)
    ((hhalf hy).monotoneOn univ).locallyBoundedVariationOn
  convert! hv using 1
  funext t
  dsimp only [ProbabilityTheory.IsSemimartingale.quadraticCovariation]
  ring
end IsSemimartingale

end ProbabilityTheory


