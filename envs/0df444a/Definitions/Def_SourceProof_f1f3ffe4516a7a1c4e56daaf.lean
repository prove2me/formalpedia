-- Prove2me | Definitions.Def_SourceProof_f1f3ffe4516a7a1c4e56daaf
-- name    : SourceProof_f1f3ffe4516a7a1c4e56daaf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:54:22.048844+00:00
-- url     : https://prove2.me/theorems/7765ee57-4744-5113-ac1f-8ae8cd616153
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_on_finiteVariation_paths

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_1275151f5edba70c876bccc8
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_42dda2460ed71edc7fce970c
import Definitions.Def_SourceProof_47027b6b170bba7ee3a3145f
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_80cb634aaa6646ad1fa02a5e
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.26: raw quadratic variation on finite-variation paths

The actual jump series is obtained from Stieltjes component integrals. The
path-local assertion does not require the FV event to have full measure.
The initial square and all positive-time endpoint jumps are retained.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_f1f3ffe4516a7a1c4e56daaf
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ → ∀ t : ℝ≥0,
      hX.quadraticVariation hF t ω = (X 0 ω) ^ 2 +
        ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2 := by
  let ha := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let hr := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  filter_upwards [(_root_.Prove2MeSourceProof.h_42dda2460ed71edc7fce970c hX) hF ha hr]
    with ω hI hv
  obtain ⟨hc, he⟩ := hI hv
  intro t
  have hi : StochLean.pathStieltjesIntegral (X · ω) hv hc.1 (ProbabilityTheory.leftLimitProcess X · ω) t =
      StochLean.pathStieltjesIncrementIntegral (X · ω) hv hc.1 (Function.leftLim (X · ω)) 0 t := by
    simp only [StochLean.pathStieltjesIntegral, _root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, zero_mul, zero_add]
    apply _root_.Prove2MeSourceProof.h_47027b6b170bba7ee3a3145f
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt hs.1)]
  change (X t ω) ^ 2 - 2 * hX.stochasticIntegral hF ha hr t ω = _
  rw [he t, hi, _root_.Prove2MeSourceProof.h_80cb634aaa6646ad1fa02a5e hv hc t,
    _root_.Prove2MeSourceProof.h_1275151f5edba70c876bccc8 hv hc.1 t]
  congr 1
  apply tsum_congr
  intro s
  simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply, ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt s.2.1)]
end IsSemimartingale

end ProbabilityTheory


