-- Prove2me | Definitions.Def_SourceProof_ae584a9168b1bd16f954b4f8
-- name    : SourceProof_ae584a9168b1bd16f954b4f8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:09.83025+00:00
-- url     : https://prove2.me/theorems/2bc60f48-6296-4640-8653-1fce46b83a8f
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.indistinguishable_unique

import Definitions.Def_SourceProof_1b5811523ebf232c3a8b514f
import Definitions.Def_SourceProof_d0a4533c9dc122ef1fd7f577
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform path convergence and a subsequence criterion for UCP

Measurability of the output compact deviations is explicit in the converse.
No continuity of an outer measure on arbitrary decreasing sets is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_ae584a9168b1bd16f954b4f8 {ι : Type*} {l : Filter ι}
    [l.NeBot] [l.IsCountablyGenerated] {X : ι → ℝ≥0 → Ω → ℝ} {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : TendstoUCP P X l Y) (hZ : TendstoUCP P X l Z)
    (hrY : HasRightContinuousPaths Y P) (hrZ : HasRightContinuousPaths Z P) :
    Indistinguishable Y Z P :=
  _root_.Prove2MeSourceProof.h_1b5811523ebf232c3a8b514f
    (fun t ↦ tendstoInMeasure_ae_unique ((_root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 hY) t) ((_root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 hZ) t)) hrY hrZ
end TendstoUCP

end ProbabilityTheory


