-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
-- name    : CountingMatroid_Analysis_RestartDrawProbeScanReplay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:21:50.691757+00:00
-- url     : https://prove2.me/theorems/9377c5a3-0c65-40a8-a4b1-9fc531201ea1
-- title:
--   An ordinal-mismatched draw probe records nothing
-- statement:
--   Fix natural $n,r$, Boolean query functions, a tape, schedule $s$, rational parameter $q$, and rational defect multipliers $w$. Let $v$ be a restart cursor with attempt count $A<R=s.\mathrm{restartCap}$. Fix a selected ordinal $\ell$, draw selector $a\in\{0,1,2\}$, and external tally $c\ne\ell$. Start the probed body with cursor $v$, false completion flag, and no captured descriptor. The supplied helper lemma states that it performs the ordinary capped chain step, retains no descriptor, and increments the tally:
--   $$D_{\mathrm{new}}=\operatorname{none},\qquad c_{\mathrm{new}}=c+1.$$
--   If the step fails, the new cursor is absent and its stop flag is true. If it succeeds with state $S'$ and position $b'$, the cursor becomes $(S',b',A+1)$ and the flag tests whether $S'$ is transversal. This is an exact returned-value identity, without positivity or oracle-correctness premises.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartDrawProbeScanReplay.lean#L133-L159

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
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
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
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
section


set_option autoImplicit false

/-!
Interval replay for the concrete ordinal probe's own accumulation, confined
to one capped return scan and lifted through the transition, stage and
restart folds. A captured descriptor can only ever change at the globally
unique attempt whose running count matches the probed ordinal; before that
attempt the probe is silent, and after it the descriptor is sticky.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.RestartAttemptAccounting















/-- INTERNAL: One guarded, allowed, ordinal-mismatched step of the probe's
body: the actual chain attempt proceeds and the probe captures nothing. -/
 theorem probedBody_ne {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n) (count : ℕ)
    (hallow : current.attempts < s.restartCap) (hne : count ≠ ordinal) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((some current, false), count), none)).val =
      match (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
      | none => some (((none, true), count + 1), none)
      | some (state, bitCursor) =>
          some (((some ⟨state, bitCursor, current.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1), none) := by
  have hne' : ¬ (current.attempts < s.restartCap ∧ count = ordinal) := fun h => hne h.2
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
    bodySite RestartAttemptAccounting.attemptIncrement Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, decide_eq_true_eq,
    Bool.false_eq_true, if_false, if_pos hallow, if_neg hne', Option.none_or]
  cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
  | none => simp
  | some result =>
    obtain ⟨state, bitCursor⟩ := result
    simp only [Arlib.Computation.Charged.val_bind]
    cases hk : (classifyState state).val with
    | invalid => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | transversal => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | defect i j => simp [Operations.successor, Arlib.Computation.Charged.val_op]















end CountingMatroid.Analysis.RestartDrawProbeScanReplay

end


