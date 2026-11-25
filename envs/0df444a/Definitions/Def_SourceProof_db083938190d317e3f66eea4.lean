-- Prove2me | Definitions.Def_SourceProof_db083938190d317e3f66eea4
-- name    : SourceProof_db083938190d317e3f66eea4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:11.242582+00:00
-- url     : https://prove2.me/theorems/ec71ac9f-3f59-431f-945b-a52d46dbe1bc
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.const_mul

import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_7fe27d80761f531095784a17
import Definitions.Def_SourceProof_ed9d54393901c01d92a26019

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear stability of the source good-integrator predicate

These results use elementary integration and its quantitative continuity
criterion. No classical decomposition or Bichteler-Dellacherie theorem is
assumed in proving stability.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_db083938190d317e3f66eea4 (hX : IsTotalSemimartingale X F P) (c : ℝ) :
    IsTotalSemimartingale (fun t ω ↦ c * X t ω) F P :=
  ⟨fun t ↦ (hX.1 t).const_mul c,
    (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc hX.2.1) (continuous_const.mul continuous_id), (_root_.Prove2MeSourceProof.h_ed9d54393901c01d92a26019 hX.2.2) c⟩
end IsTotalSemimartingale

end ProbabilityTheory


