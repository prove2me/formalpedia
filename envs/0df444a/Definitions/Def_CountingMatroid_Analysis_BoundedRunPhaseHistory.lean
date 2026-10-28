-- Prove2me | Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
-- name    : CountingMatroid_Analysis_BoundedRunPhaseHistory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:07:02.249243+00:00
-- url     : https://prove2.me/theorems/473dc9a6-2674-4bb0-964d-b75e619938b8
-- title:
--   Actual phase histories and first ratio failure
-- statement:
--   For a ground size $n$ and schedule $s$, the initial annealing cursor uses the actual initial-weight and learned-table allocations, accumulated product one, and bit cursor zero. Given natural rank parameter $r$, Boolean subset oracles, and a Boolean tape, the phase history after $j$ steps is the optional value of $j$ successive bounded phase operations from that initial cursor. Failure remains present as an absent cursor.
--
--   For input parameters $p$, let $s=\operatorname{setup}(n,p)$ and let $C_j$ be the transversal partition sum at activity $s.\rho^j$. A good phase-ratio step at $j$ requires an actually reached cursor $u$, a successful next phase cursor $v$, positive products $u.\mathrm{product}$ and $v.\mathrm{product}$, and
--   $$
--   \frac{1-s.\eta}{1+s.\eta}
--   \le
--   \frac{v.\mathrm{product}/u.\mathrm{product}}{C_{j+1}/C_j}
--   \le
--   \frac{1+s.\eta}{1-s.\eta}.
--   $$
--   The predicate imposes these explicit inequalities; rational division remains totalized, and no extra partition-positivity hypothesis is inserted.
--
--   The first phase-ratio failure predicate is
--   $$
--   \exists j<s.L:\quad
--   \bigl(\forall i<j,\ \operatorname{PhaseRatioStep}(i)\bigr)
--   \ \land\ \neg\operatorname{PhaseRatioStep}(j).
--   $$
--   It covers failure of the actual transition or of any other requirement of the ratio-step predicate. It includes no separate nonzero-output guard.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunPhaseHistory.lean#L18-L23

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

/-- INTERNAL: The initial cursor is the value of the actual allocations in
`boundedRun`; no independently chosen learned tables are supplied.
TEXLINE: main.tex:1152-1160 -/
noncomputable def initialCursor (n : ℕ) (s : AnnealingSchedule) : AnnealingCursor n :=
  let weights := (initialWeights n).val
  ⟨(allocateLearnedWeights n s.L weights).val, weights, 1, 0⟩

/-- INTERNAL: Prefix states of the actual charged phase fold. `none` retains
all abort branches, rather than conditioning on a completed run.
TEXLINE: main.tex:1160-1205 -/
noncomputable def phaseHistory {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    Option (AnnealingCursor n) :=
  (Arlib.Computation.Charged.repeatFor
    (boundedRunPhase r o₁ o₂ tape s) j (some (initialCursor n s))).val







/-- INTERNAL: A local good phase requires a successful transition from the
actually reached cursor, positive accumulated products, and the relative
ratio bounds. The quotient of consecutive products recovers the executed
ratio, so a separate independently chosen ratio sequence is unnecessary.
TEXLINE: main.tex:1273-1296 -/
def PhaseRatioStep {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) (j : ℕ) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun k => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ k)
  ∃ current next : AnnealingCursor n,
    phaseHistory r o₁ o₂ tape s j = some current ∧
    (boundedRunPhase r o₁ o₂ tape s j (some current)).val = some next ∧
    0 < current.product ∧ 0 < next.product ∧
    (1 - s.η) / (1 + s.η) ≤
      (next.product / current.product) / (C (j + 1) / C j) ∧
    (next.product / current.product) / (C (j + 1) / C j) ≤
      (1 + s.η) / (1 - s.η)



/-- INTERNAL: Partition unsuccessful histories by the first phase whose
actual transition aborts or whose accumulated-product ratio is inaccurate.
This predicate imposes no nonzero-output guard.
TEXLINE: main.tex:1273-1287 -/
def FirstPhaseRatioFailure {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) : Prop :=
  ∃ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
    (∀ i < j, PhaseRatioStep r o₁ o₂ p tape i) ∧
    ¬ PhaseRatioStep r o₁ o₂ p tape j



end CountingMatroid.Analysis.BoundedRunPhaseHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · represented actual phase-fold prefixes; proved their successor relation and final-output equality, reconstructed an accurate-ratio witness from successful local steps, and covered witness failure by the first failed phase. No probability estimate or unproved declaration introduced.
-/

end


