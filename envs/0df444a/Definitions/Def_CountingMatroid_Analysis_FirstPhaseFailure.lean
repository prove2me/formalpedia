-- Prove2me | Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
-- name    : CountingMatroid_Analysis_FirstPhaseFailure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:07:05.507199+00:00
-- url     : https://prove2.me/theorems/730ccd04-af91-4c5e-b403-fed954c84f1b
-- title:
--   Defect partitions, good tables, and first phase-certificate failure
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean query functions, and put $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ with natural subtraction. For rational $q$ and distinct indices $(i,k)$, define
--   $$D_{ik}(q)=\sum_{S\text{ classified defect }(i,k)}q^{d(S)}.$$
--   Fix a schedule with factor $\rho$, phase count $L$, and tolerance $\eta$. Write $C_a$ for the transversal partition at $\rho^a$ and $I_{a,ik}=C_a/D_{ik}(\rho^a)$. A cursor is good at level $j$ if every stored multiplier at every $a\le j$ lies in $[I_{a,ik}/4,4I_{a,ik}]$, and its current multipliers satisfy this at $j$.
--   A phase-$j$ certificate on a given tape supplies actual reached and successful next cursors $v,v'$ from the prescribed initialized loop, goodness of $v$, and a rational $z$ satisfying
--   $$\frac{1-\eta}{1+\eta}\le\frac{z}{C_{j+1}/C_j}\le\frac{1+\eta}{1-\eta},\qquad v'.\mathrm{product}=v.\mathrm{product}\,z.$$
--   It requires goodness of $v'$ at $j+1$ only when $j+1<L$. Initialization uses the prescribed weights and table allocation, product one, and bit position zero. First certificate failure is
--   $$\operatorname{FirstFailure}(j)\Longleftrightarrow(\forall a<j,\operatorname{CertifiedPhase}(a))\land\neg\operatorname{CertifiedPhase}(j).$$
--   These are predicates, with no oracle-correctness or positivity assumptions built into their definitions; rational division is total.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FirstPhaseFailure.lean#L23-L32

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
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

/-!
A local failure event for the actual charged phase prefixes. A certificate
requires completion, an accurate ratio, and good stored multipliers. First
failure events partition failure of these certificates, including aborts.
The per-phase finite-tape probability estimate remains in the consuming theorem;
it requires the paper's conditional restart and observation analysis and the
adaptive finite-tape coupling. No independence of adjacent phase events is
assumed by this representation.
-/

namespace CountingMatroid.Analysis.FirstPhaseFailure

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

/-- INTERNAL: The unweighted partition sum of one ordered defect class,
evaluated using the program's paired-rank and state-classification scans.
TEXLINE: main.tex:712-735 -/
noncomputable def defectPartition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (index : DefectIndex n) : ℚ := by
  classical
  exact ∑ state : PairedSet n,
    if (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0

/-- INTERNAL: The paper's factor-four condition on every table used by a
restart and on the current phase's multipliers, at their respective parameters.
TEXLINE: main.tex:733-735,1207-1285 -/
def GoodStoredMultipliers {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n) : Prop :=
  let ideal := fun a index =>
    TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a) /
      defectPartition r o₁ o₂ (s.ρ ^ a) index
  (∀ a ≤ j, ∀ index,
    ideal a index / 4 ≤ current.tables a index ∧
      current.tables a index ≤ 4 * ideal a index) ∧
  ∀ index, ideal j index / 4 ≤ current.currentWeights index ∧
    current.currentWeights index ≤ 4 * ideal j index

/-- INTERNAL: A certificate of one actual phase step, retaining its reached
cursor, its product update, and the good tables needed for the next restart.
The prefix is the value of the exact `boundedRun` loop with its actual
allocations. Final-phase tables need no guarantee at the unused level `L`.
TEXLINE: main.tex:1160-1205,1257-1296 -/
def CertifiedPhase {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  let weights := (initialWeights n).val
  let initial : AnnealingCursor n :=
    ⟨(allocateLearnedWeights n s.L weights).val, weights, 1, 0⟩
  let phaseValue := (Arlib.Computation.Charged.repeatFor
    (boundedRunPhase r o₁ o₂ tape s) j (some initial)).val
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  ∃ ratio : ℚ,
    (1 - s.η) / (1 + s.η) ≤ ratio / (C (j + 1) / C j) ∧
    ratio / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η) ∧
    ∃ current next : AnnealingCursor n,
      phaseValue = some current ∧
      (boundedRunPhase r o₁ o₂ tape s j (some current)).val = some next ∧
      next.product = current.product * ratio ∧
      GoodStoredMultipliers r o₁ o₂ s j current ∧
      (j + 1 < s.L → GoodStoredMultipliers r o₁ o₂ s (j + 1) next)

/-- INTERNAL: First failure of the local phase certificates. Earlier
certificates retain the learned-weight invariant, rather than conditioning
only on earlier ratio accuracy.
TEXLINE: main.tex:1271-1285 -/
def FirstFailure {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  (∀ a < j, CertifiedPhase r o₁ o₂ tape s a) ∧
    ¬ CertifiedPhase r o₁ o₂ tape s j



end CountingMatroid.Analysis.FirstPhaseFailure

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · partial · after mechanical handoff rejection, closed `uncertified_card_le_sum` and retained the operational certificate definitions; the unproved per-phase budget remains inside the assigned parent, rather than in a new exported declaration.
* r18 · open · finite-set conversion and ENNReal denominator normalization expose the exact first-failure counting inequality. The uniform conditional suffix estimate still needs restart expectation, stationary-mean observation MSE, learned-table preservation, and finite-tape coverage. Parent imports and uses this budget in a checked finite union bound.
-/

end


