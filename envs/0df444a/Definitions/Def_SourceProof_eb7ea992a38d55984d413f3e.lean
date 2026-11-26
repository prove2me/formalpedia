-- Prove2me | Definitions.Def_SourceProof_eb7ea992a38d55984d413f3e
-- name    : SourceProof_eb7ea992a38d55984d413f3e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:20:33.117771+00:00
-- url     : https://prove2.me/theorems/31ccbbc1-8aab-51a2-a8ad-f782ee6d7c43
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isComplexSemimartingale_stochasticAreaExponent

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticArea_Exponent_F000
import Definitions.Def_SourceProof_220df0c636bc8e6794b6674d
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_5fba6145a988c3f8a6970ab9
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_b3fcce5bc84221b19067070f
import Definitions.Def_SourceProof_ba54eeb3a2661e253611936f
import Definitions.Def_SourceProof_cec55a75e8011931c820c0c2
import Definitions.Def_SourceProof_ced45e1f2317b8656a5b47cf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual Riccati-compensated area exponential

The clock is explicit: it may be deterministic time or the existing continuous
bracket. The process is constructed from the actual area integral, and its
semimartingale, continuity, endpoint and norm properties are proved here.
The local-martingale property still requires the stochastic drift calculation.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_eb7ea992a38d55984d413f3e
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P) (u T : ℝ) :
    IsComplexSemimartingale (hX.stochasticAreaExponent hY hF Q u T) F P := by
  have hα := (_root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9 hQ) hF (_root_.Prove2MeSourceProof.h_220df0c636bc8e6794b6674d u T)
  have hβ := (_root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9 hQ) hF (_root_.Prove2MeSourceProof.h_b3fcce5bc84221b19067070f u T)
  have hR := (_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d ((_root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9 hX) hF (show ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) by fun_prop)))
    ((_root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9 hY) hF (show ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) by fun_prop))
  exact (_root_.Prove2MeSourceProof.h_cec55a75e8011931c820c0c2 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 ((_root_.Prove2MeSourceProof.h_ba54eeb3a2661e253611936f hα) hR hF)) (-(1 / 2 : ℝ)))) hβ))
    ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 ((_root_.Prove2MeSourceProof.h_ced45e1f2317b8656a5b47cf hX) hY hF)) u)
end IsSemimartingale

end ProbabilityTheory


