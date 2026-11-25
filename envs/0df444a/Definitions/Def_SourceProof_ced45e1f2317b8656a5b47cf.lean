-- Prove2me | Definitions.Def_SourceProof_ced45e1f2317b8656a5b47cf
-- name    : SourceProof_ced45e1f2317b8656a5b47cf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:46:10.826233+00:00
-- url     : https://prove2.me/theorems/7fe24a8b-c09f-4d1b-b9b7-376567ac7f42
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_stochasticArea

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticArea_Basic_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_76e6f1c00540bd94935e0dc0
import Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
import Definitions.Def_SourceProof_d0e331387f6701b34b2c711d
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual antisymmetric stochastic area integral

The source area is `integral X_- dY - integral Y_- dX`, using the sole
Chapter II stochastic integral. It is twice the signed geometric area in
Protter's convention. It starts at zero even for arbitrary initial values.
Continuous local-martingale coordinates give a continuous local martingale;
neither Brownian laws nor a bracket formula are built into the definition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_ced45e1f2317b8656a5b47cf
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.stochasticArea hY hF) F P :=
  (_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba ((_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hY) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
      (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))))
    ((_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hX) hF
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
        (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)))
end IsSemimartingale

end ProbabilityTheory


