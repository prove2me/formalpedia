-- Prove2me | Definitions.Def_CountingMatroid_Analysis_TransversalPartition
-- name    : CountingMatroid_Analysis_TransversalPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:06.38027+00:00
-- url     : https://prove2.me/theorems/b33d9e4e-1144-45af-99ae-66ed9e86e56d
-- title:
--   Transversal states, operational deficiencies, and partition sums
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be Boolean query functions on subsets of $[n]=\{0,\ldots,n-1\}$. Put $E=[n]\times\{0,1\}$, let paired states be subsets of $E$, and write $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ using truncated natural subtraction. A transversal has one label in each pair; a defect $(i,k)$ has empty pair $i$, full pair $k$, and one label elsewhere, with $i\ne k$. For $A\subseteq[n]$, define
--   $$T(A)=\{(i,0):i\in A\}\cup\{(i,1):i\notin A\},\qquad d_T(A)=d(T(A)).$$
--   For any rational parameter $q$, the transversal partition is
--   $$C(q)=\sum_{A\subseteq[n]}q^{d_T(A)}.$$
--   The exponent is the value from the program's paired-rank scans. These definitions allow arbitrary query functions and rational $q$; an exact matroid-rank interpretation or positive-weight probability law requires separate hypotheses.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TransversalPartition.lean#L13-L17

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
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.TransversalPartition

open CountingMatroid.Model

/-- INTERNAL: The paired state corresponding to an original-ground subset;
false marks its selected x elements and true marks its complementary y elements.
TEXLINE: main.tex:270-281 -/
def transversalState {n : ℕ} (A : Finset (Fin n)) : PairedSet n :=
  Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A)))

/-- INTERNAL: Rank deficiency of a transversal, calculated by the same paired
rank scan used by the bounded run.
TEXLINE: main.tex:292-316,1333-1346 -/
noncomputable def transversalDeficiency {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (A : Finset (Fin n)) : ℕ :=
  n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
    (transversalState A)).val

/-- INTERNAL: The paper's analytical transversal partition sum, expressed over
the concrete rank deficiencies used in `Program.weightOfKind`.
TEXLINE: main.tex:307-316 -/
noncomputable def partitionSum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) : ℚ :=
  ∑ A : Finset (Fin n), q ^ transversalDeficiency r o₁ o₂ A









end CountingMatroid.Analysis.TransversalPartition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r10 · conditional · closed the contamination calculation for all n using a new rank-scan bridge; the bridge still has a `sorry` and its requested scheduler handoff was refused.
* r9 · partial · proved the generic power-sum comparison, nonnegative schedule weight, and exact schedule field identities; rank-scan correctness and the final tail estimate remain open.
* r8 · open · direct simplification exposes the missing paired-rank correctness theorem and the final schedule tail bound.
-/

end


