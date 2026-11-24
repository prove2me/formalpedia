-- Prove2me | Definitions.Def_SourceProof_d0a4533c9dc122ef1fd7f577
-- name    : SourceProof_d0a4533c9dc122ef1fd7f577
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:28.317554+00:00
-- url     : https://prove2.me/theorems/bc524019-e521-4d2c-aad2-170712f1fa92
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.fixedTime

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 {ι : Type*} {X : ι → ℝ≥0 → Ω → ℝ}
    {l : Filter ι} (hX : TendstoUCP P X l Y) (t : ℝ≥0) :
    TendstoInMeasure P (fun i ↦ X i t) l (Y t) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hX t ε hε)
    (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  intro ω hω
  change ε ≤ edist (X i t ω) (Y t ω) at hω
  rw [edist_dist, dist_eq_norm_sub] at hω
  exact hω.trans (_root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 (X := X i) (Y := Y) (t := t) le_rfl ω)
end TendstoUCP

end ProbabilityTheory


