-- Prove2me | Definitions.Def_SourceProof_b28a2172c9a8685639607df3
-- name    : SourceProof_b28a2172c9a8685639607df3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:58:32.269935+00:00
-- url     : https://prove2.me/theorems/1b23f72a-c035-54bb-a5a1-bfa8d7f3c83c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.integrationByParts

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_925a6c152cedf8b9c9d6d57e
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integration by parts and the algebra of semimartingales

The identity is deduced from actual random-partition mixed sums and the
cadlag-integrand Riemann theorem. It identifies the existing polarized bracket;
the product formula is not used as a competing definition of covariation.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_b28a2172c9a8685639607df3
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (X * Y)
      (hY.stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) +
      hX.stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)) + hX.quadraticCovariation hY hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_925a6c152cedf8b9c9d6d57e hX) hY hF] with ω hω t
  simp only [Pi.add_apply, hω t, Pi.sub_apply]
  ring
end IsSemimartingale

end ProbabilityTheory


