-- Prove2me | Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
-- name    : CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:03:23.232979+00:00
-- url     : https://prove2.me/theorems/daa5fa37-8a11-4ab4-9b85-eabd718972ad
-- title:
--   Empirical update of defect multipliers
-- statement:
--   Let $s$ be a schedule with phase count $L$, let $j\in\mathbb N$, and let $w_{ik}\in\mathbb Q$ be old defect multipliers for distinct indices in $[n]$. An observation cursor supplies a natural transversal count $c_0$ and defect counts $c_{ik}$. Define
--   $$w'_{ik}=\begin{cases}w_{ik}c_0/c_{ik}&j+1<L,\\w_{ik}&j+1\ge L.\end{cases}$$
--   The original multiplier is used once per defect. The definition is total even at $c_{ik}=0$; successful finishing checks and nonzero-count hypotheses are separate. Common sample-count normalization cancels in the intended empirical ratio.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FinishPhaseEmpiricalUpdate.lean#L37-L46

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program





/-- INTERNAL: Exact empirical update computed by the successful finish scan.
The formula uses the original multiplier once for each off-diagonal index;
normalizing both counts by the observation count cancels.
TEXLINE: main.tex:1181-1201,1257-1270 -/
noncomputable def empiricalWeights {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n) : Multipliers n :=
  fun index => if j + 1 < s.L then
    weights index * (observed.counts .transversal : ℚ) /
      (observed.counts (.defect index.emptyPair index.fullPair) : ℚ)
    else weights index



end CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · evaluated the optional nested scan via a duplicate-free
  product of index lists; each off-diagonal multiplier is updated exactly once.
  Positive counts remove aborts and common observation normalization cancels.
* recovery · rejected handoff · scheduler mechanically rejected the finishing
  lemma without a further diagnostic; retained ownership and proved it locally.
-/

end


