-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
-- name    : CountingMatroid_Analysis_ConditionalDefectCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:18.153923+00:00
-- url     : https://prove2.me/theorems/b6b6c730-7c27-42dc-9ae3-92c03727f163
-- title:
--   Partial assignments and conditional defect totals
-- statement:
--   Let $E=\{0,\ldots,n-1\}\times\{0,1\}$. An assignment is a function $\sigma:\{0,\ldots,n-1\}\to\operatorname{Option}\{0,1\}$. A paired state $S\subseteq E$ respects $\sigma$ if an assigned label $(i,b)$ is present and its mate $(i,1-b)$ is absent. On the original subset indexing, $A\subseteq\{0,\ldots,n-1\}$ respects $\sigma$ when each assigned $b$ equals $[i\notin A]$.
--
--   For arbitrary Boolean subset oracles $o_1,o_2$, natural rank parameter $r$, and rational activity $q$, define
--   $$
--   T_\sigma=\sum_{A\text{ respects }\sigma}q^{d(A)},\qquad
--   D_\sigma(e,f)=
--   \sum_{\substack{S\text{ respects }\sigma\\
--   \operatorname{classify}(S)=\operatorname{defect}(e,f)}}
--   q^{\,n-\operatorname{pairedRank}(S)}.
--   $$
--   Here $d$ and $\operatorname{pairedRank}$ are the operational deficiency and rank scan for $r,o_1,o_2$; the exponent subtraction is natural-number subtraction. The defect index specifies distinct empty and full pair indices $e,f$. These totals impose no positivity assumption on $q$ or matroid-correctness assumption on the oracles.
--
--   The distinguished completion places both labels in pair $f$, none in pair $e$, and exactly one label in each other pair $i$, choosing $\sigma(i)$ when assigned and false otherwise:
--   $$
--   S_{\sigma;e,f}=\{(i,\sigma(i).\operatorname{getD}(0)):i\ne e,f\}
--   \cup\{(f,0),(f,1)\}.
--   $$
--   This construction itself does not require that $e$ and $f$ be unassigned.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConditionalDefectCoefficients.lean#L17-L19

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
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
import Mathlib.Data.List.Induction
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
Conditional transversal and defect totals for the operational rank weights.
The empty assignment recovers the existing partition sums. Positivity and
binary splitting below concern these finite sums; the quadratic signature
inequalities are separate mathematical obligations.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.TransversalPartition

/-- PAPER: main.tex:383-386
A partial transversal specifies the selected element at each assigned pair. -/
abbrev Assignment (n : ℕ) := Fin n → Option Bool

/-- PAPER: main.tex:383-389
Respecting an assignment requires the chosen element and excludes its mate. -/
def Respects {n : ℕ} (σ : Assignment n) (state : PairedSet n) : Prop :=
  ∀ i b, σ i = some b → (i, b) ∈ state ∧ (i, !b) ∉ state

/-- INTERNAL: Express the same assignment on the original subset indexing
transversals, with false selecting x and true selecting y.
TEXLINE: main.tex:383-389 -/
def SubsetRespects {n : ℕ} (σ : Assignment n) (A : Finset (Fin n)) : Prop :=
  ∀ i b, σ i = some b → decide (i ∉ A) = b

/-- PAPER: main.tex:383-392
The conditional transversal total uses the actual operational deficiency. -/
noncomputable def transversalTotal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n) : ℚ := by
  classical
  exact ∑ A : Finset (Fin n),
    if SubsetRespects σ A then q ^ transversalDeficiency r o₁ o₂ A else 0

/-- PAPER: main.tex:386-392
The conditional unmultiplied ordered-defect total uses the operational
classifier and paired-rank scan, with the empty/full indices unassigned. -/
noncomputable def defectTotal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (index : DefectIndex n) : ℚ := by
  classical
  exact ∑ state : PairedSet n,
    if Respects σ state ∧
      (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0













/-- INTERNAL: Complete a partial assignment to the specified defect class;
unassigned ordinary pairs select x.
TEXLINE: main.tex:383-392 -/
def defectCompletion {n : ℕ} (σ : Assignment n) (index : DefectIndex n) : PairedSet n :=
  ((Finset.univ.erase index.emptyPair).erase index.fullPair).image
    (fun i => (i, (σ i).getD false)) ∪
      {(index.fullPair, false), (index.fullPair, true)}









end CountingMatroid.Analysis.ConditionalDefectCoefficients

end


