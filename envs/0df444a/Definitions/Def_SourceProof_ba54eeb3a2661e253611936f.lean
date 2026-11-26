-- Prove2me | Definitions.Def_SourceProof_ba54eeb3a2661e253611936f
-- name    : SourceProof_ba54eeb3a2661e253611936f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:55:28.193479+00:00
-- url     : https://prove2.me/theorems/65a33928-11e7-4538-8194-9cc5d1b1753d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.mul

import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_2805187910815ebae4f90f84
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
import Definitions.Def_SourceProof_9a15eada3555a513322a1de0
import Definitions.Def_SourceProof_b28a2172c9a8685639607df3
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba

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
theorem _root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f (hX : IsSemimartingale X F P)
    (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (X * Y) F P := by
  have hJY := (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hY) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
    (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  have hJX := (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hX) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
    (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
  exact (_root_.Prove2MeSourceProof.h_2805187910815ebae4f90f84 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hJY) hJX)) ((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 hX) hY hF)))
    (_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 ((_root_.Prove2MeSourceProof.h_b28a2172c9a8685639607df3 hX) hY hF)) (fun t ↦ ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t).mul ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY) t))
end IsSemimartingale

end ProbabilityTheory


