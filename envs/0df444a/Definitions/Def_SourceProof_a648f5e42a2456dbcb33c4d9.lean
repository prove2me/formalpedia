-- Prove2me | Definitions.Def_SourceProof_a648f5e42a2456dbcb33c4d9
-- name    : SourceProof_a648f5e42a2456dbcb33c4d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:47:44.815346+00:00
-- url     : https://prove2.me/theorems/ed452145-becc-532a-890c-abae53d9021e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_quadraticVariation

import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_237ca6993b1d0487e6b85da5
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_98bda33797c63c6cacfeb839

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Increasing paths of the canonical raw quadratic variation

The partial-cell square sums are not assumed monotone. Evaluating each sum
at the next partition endpoint produces monotone completed-cell sums. A
locally uniform subsequence and right continuity identify their pointwise
limit with the raw bracket on one event for all times together.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_a648f5e42a2456dbcb33c4d9
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.quadraticVariation hF) F P :=
  (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f ((_root_.Prove2MeSourceProof.h_237ca6993b1d0487e6b85da5 hX) hF))
    ((_root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839 hX) hF) hF ((_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hX) hF)
end IsSemimartingale

end ProbabilityTheory


