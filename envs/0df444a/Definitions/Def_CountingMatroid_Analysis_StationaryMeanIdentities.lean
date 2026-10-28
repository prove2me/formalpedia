-- Prove2me | Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
-- name    : CountingMatroid_Analysis_StationaryMeanIdentities
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:45.789373+00:00
-- url     : https://prove2.me/theorems/6259de55-d234-4580-b61e-505796c93c2c
-- title:
--   Operational state weights and normalized mean identities
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be Boolean query functions on subsets of $[n]=\{0,\ldots,n-1\}$. Put $E=[n]\times\{0,1\}$, let paired states be subsets of $E$, and write $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ using truncated natural subtraction. A transversal has one label in each pair; a defect $(i,k)$ has empty pair $i$, full pair $k$, and one label elsewhere, with $i\ne k$. For rational $q$ and rational defect multipliers $w_{ik}$, define $W(S)$ as the optional weight returned by the program's classifier/weight routine, with absence replaced by zero, and set
--   $$Z=\sum_S W(S),\qquad m_\kappa=\frac{\sum_{S:\operatorname{kind}(S)=\kappa}W(S)}{Z},\qquad
--   m_U=\frac{\sum_{S\text{ transversal}}W(S)\rho^{d(S)}}{Z},$$
--   where $\rho\in\mathbb Q$ and $\kappa$ is any state kind. The supplied helper lemmas identify $W(S)=q^{d(S)}$ on transversals and $W(S)=w_{ik}q^{d(S)}$ on a distinct ordered defect class. Invalid states have weight zero.
--   Write $C(q)=\sum_{A\subseteq[n]}q^{d(T(A))}$, where $T(A)$ selects label zero on $A$ and one elsewhere, and let $D_{ik}(q)$ sum $q^{d(S)}$ over defect $(i,k)$. The included mean-identity theorem assumes $q>0$ and every $w_{ik}>0$ and proves
--   $$Z>0,\qquad m_{\mathrm{transversal}}=\frac{C(q)}Z,\qquad m_U=\frac{C(q\rho)}Z,\qquad m_{ik}=\frac{w_{ik}D_{ik}(q)}Z.$$
--   The parameter $\rho$ remains arbitrary. Without the positivity hypotheses the definitions still use total rational division. No exact-oracle assumption is present; these identities do not assert stationarity of a capped transition or a physical implementation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryMeanIdentities.lean#L11-L16

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.StationaryMeanIdentities

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The program's exact Metropolis state weight, extended by zero
to states its classifier rejects. This definition uses the executable scans.
TEXLINE: main.tex:721-728,746-751 -/
noncomputable def stateWeight {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n) : ℚ :=
  (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val.getD 0

/-- INTERNAL: Normalizing constant of the finite state-weight law. No
claim about a capped transition's stationarity is made by this definition.
TEXLINE: main.tex:721-728 -/
noncomputable def normalizer {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) : ℚ :=
  ∑ state : PairedSet n, stateWeight r o₁ o₂ q weights state

/-- INTERNAL: Type-indicator mean under the normalized state weights.
TEXLINE: main.tex:1241-1247 -/
noncomputable def typeMean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (kind : StateKind n) : ℚ :=
  (∑ state : PairedSet n,
    if (classifyState state).val = kind then stateWeight r o₁ o₂ q weights state else 0) /
      normalizer r o₁ o₂ q weights

/-- INTERNAL: Mean of the same observable added by `recordObservation`:
zero on defects and the cooling factor to the paired deficiency on transversals.
TEXLINE: main.tex:1181-1187,1241-1247 -/
noncomputable def numeratorMean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q ρ : ℚ) (weights : Multipliers n) : ℚ :=
  (∑ state : PairedSet n,
    if (classifyState state).val = .transversal then
      stateWeight r o₁ o₂ q weights state *
        ρ ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0) / normalizer r o₁ o₂ q weights

/-- INTERNAL: Evaluate the exact program weight on an accepted transversal.
TEXLINE: main.tex:721-728 -/
 theorem state_weight_transversal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (hkind : (classifyState state).val = .transversal) :
    stateWeight r o₁ o₂ q weights state =
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
  simp [stateWeight, hkind, weightOfKind, natSub,
    CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support]

/-- INTERNAL: Evaluate the exact program weight on an accepted ordered defect.
TEXLINE: main.tex:721-728 -/
 theorem state_weight_defect {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (index : DefectIndex n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    stateWeight r o₁ o₂ q weights state = weights index *
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
  simp [stateWeight, hkind, weightOfKind, index.distinct, natSub,
    CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support, multiplierRead, ratMul]

/-- INTERNAL: The normalized operational state weights have the paper's
type and annealing-observable mean identities. Stationarity for the ideal
Metropolis kernel and coupling to the capped draws remain separate obligations.
TEXLINE: main.tex:721-728,1241-1247 -/
theorem stationary_mean_identities {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q ρ : ℚ) (weights : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < weights index) :
    let Z := normalizer r o₁ o₂ q weights
    0 < Z ∧
      typeMean r o₁ o₂ q weights .transversal =
        TransversalPartition.partitionSum r o₁ o₂ q / Z ∧
      numeratorMean r o₁ o₂ q ρ weights =
        TransversalPartition.partitionSum r o₁ o₂ (q * ρ) / Z ∧
      ∀ index, typeMean r o₁ o₂ q weights
        (.defect index.emptyPair index.fullPair) =
        weights index * FirstPhaseFailure.defectPartition r o₁ o₂ q index / Z := by
  classical
  have hnonneg (state : PairedSet n) : 0 ≤ stateWeight r o₁ o₂ q weights state := by
    cases hkind : (classifyState state).val with
    | invalid => simp [stateWeight, hkind, weightOfKind]
    | transversal =>
        rw [state_weight_transversal r o₁ o₂ q weights state hkind]
        exact (pow_pos hq _).le
    | defect i j =>
        by_cases hij : i ≠ j
        · rw [state_weight_defect r o₁ o₂ q weights state ⟨i, j, hij⟩ hkind]
          exact (mul_pos (hw _) (pow_pos hq _)).le
        · simp [stateWeight, hkind, weightOfKind, hij]
  have hCsum : (∑ state : PairedSet n,
      if (classifyState state).val = .transversal then
        stateWeight r o₁ o₂ q weights state else 0) =
      TransversalPartition.partitionSum r o₁ o₂ q := by
    rw [← TransversalClassPartition.transversal_class_partition r o₁ o₂ q]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs with hkind
    · exact state_weight_transversal r o₁ o₂ q weights state hkind
    · rfl
  have hCpos : 0 < TransversalPartition.partitionSum r o₁ o₂ q := by
    apply Finset.sum_pos
    · intro A _
      exact pow_pos hq _
    · exact Finset.univ_nonempty
  have hCbound : TransversalPartition.partitionSum r o₁ o₂ q ≤
      normalizer r o₁ o₂ q weights := by
    rw [← hCsum]
    apply Finset.sum_le_sum
    intro state _
    split_ifs
    · exact le_rfl
    · exact hnonneg state
  have hZ : 0 < normalizer r o₁ o₂ q weights := hCpos.trans_le hCbound
  refine ⟨hZ, ?_, ?_, ?_⟩
  · exact congrArg (· / normalizer r o₁ o₂ q weights) hCsum
  · unfold numeratorMean
    apply congrArg (· / normalizer r o₁ o₂ q weights)
    rw [← TransversalClassPartition.transversal_class_partition r o₁ o₂ (q * ρ)]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs with hkind
    · rw [state_weight_transversal r o₁ o₂ q weights state hkind, mul_pow]
    · rfl
  · intro index
    unfold typeMean
    apply congrArg (· / normalizer r o₁ o₂ q weights)
    unfold FirstPhaseFailure.defectPartition
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs with hkind
    · exact state_weight_defect r o₁ o₂ q weights state index hkind
    · exact (mul_zero _).symm

end CountingMatroid.Analysis.StationaryMeanIdentities

end


