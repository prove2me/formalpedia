-- Prove2me | Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
-- name    : CountingMatroid_Analysis_PhaseObservationExperiment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:11:00.320743+00:00
-- url     : https://prove2.me/theorems/b9cb7fa9-f9af-4473-bf8a-613e8045dac7
-- title:
--   Operational observation data and squared estimation error
-- statement:
--   Fix natural parameters $n,r$, Boolean subset oracles, a tape, a schedule $s$, and phase $j$. The phase-observation data first follow the actual phase history, then restart from its reached cursor, and finally observe with activity $s.\rho^j$ and its current weights. The result is either the reached annealing cursor together with the observation cursor, or failure if any component fails.
--
--   Observable indices form $\{0,1\}\sqcup(G\times G)$, where $G=\{0,\ldots,n-1\}$. The Boolean indices select the transversal indicator and annealing numerator. An ordered pair $(i,k)$ selects the defect-class indicator when $i\ne k$ and the transversal indicator when $i=k$. Their means $\mu_a$ are the operational type means or numerator mean at the reached weights; empirical means $\widehat\mu_a$ divide the corresponding count or numerator sum by $m=s.\mathrm{observations}$.
--
--   The completion predicate additionally requires good stored multipliers at the reached cursor and $m>0$. For an observable index $a$, define
--   $$
--   E_a=
--   \begin{cases}
--   (\widehat\mu_a-\mu_a)^2,&\text{observation data exist, stored multipliers are good, and }m>0,\\
--   0,&\text{otherwise}.
--   \end{cases}
--   $$
--   This retains a second moment on successful good executions without assigning estimates to aborts.
--
--   For input parameters $p$, a successful phase prefix is a prefix obtained from some Boolean tape of the prescribed block length whose phases $i<j$ are certified. It is the tape truncated at the actually reached cursor, or at zero if the phase history is absent. Cursor coverage and success of the current phase are not extra premises of this prefix definition.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseObservationExperiment.lean#L11-L21

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
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
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

namespace CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: The reached phase cursor and the actual observation output,
retaining every restart and observation abort as `none`.
TEXLINE: main.tex:1163-1187,1207-1266 -/
noncomputable def phaseObservationData {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) :
    Option (AnnealingCursor n × ObservationCursor n) := do
  let current ← BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j
  let start ← (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val
  let observed ← (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val
  pure (current, observed)

/-- INTERNAL: Reindex type observables by pairs, with diagonal pairs repeating
 the transversal indicator. The two Boolean indices are the transversal
 indicator and the annealing numerator. This keeps the empty-defect case.
TEXLINE: main.tex:1241-1263 -/
abbrev Observable (n : ℕ) := Bool ⊕ (Fin n × Fin n)

/-- INTERNAL: The stationary mean of one concrete operational observable.
TEXLINE: main.tex:1241-1255 -/
noncomputable def observableMean {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (index : Observable n) : ℚ :=
  match index with
  | .inl false => typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights .transversal
  | .inl true => numeratorMean r o₁ o₂ (s.ρ ^ j) s.ρ current.currentWeights
  | .inr (i, k) => typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights
      (if i = k then .transversal else .defect i k)

/-- INTERNAL: The empirical mean read from the actual observation counters.
TEXLINE: main.tex:1181-1187 -/
noncomputable def empiricalMean {n : ℕ} (s : AnnealingSchedule)
    (observed : ObservationCursor n) (index : Observable n) : ℚ :=
  match index with
  | .inl false => (observed.counts .transversal : ℚ) / s.observations
  | .inl true => observed.numeratorSum / s.observations
  | .inr (i, k) =>
      (observed.counts (if i = k then .transversal else .defect i k) : ℚ) / s.observations

/-- INTERNAL: Separate operational completion from relative estimation error.
This predicate includes the deterministic invariant and a nonempty sample.
TEXLINE: main.tex:1207-1266 -/
def ObservationCompleted {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  ∃ current observed, phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
    FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧ 0 < s.observations

/-- INTERNAL: Squared deviation on completed good executions, and zero on
all other executions. This is a subprobability second moment; aborts are
bounded separately, rather than assigned an artificial empirical estimate.
TEXLINE: main.tex:1253-1266 -/
noncomputable def observationSquaredError {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (index : Observable n) : ℚ := by
  classical
  exact match phaseObservationData r o₁ o₂ tape s j with
  | none => 0
  | some (current, observed) =>
      if FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧ 0 < s.observations
      then (empiricalMean s observed index - observableMean r o₁ o₂ s j current index) ^ 2
      else 0







/-- INTERNAL: A consumed prefix of an actual finite run whose earlier
phase certificates all hold. Cursor coverage is deliberately an obligation
of the quantitative phase estimates, not a premise imposed on callers.
TEXLINE: main.tex:1207-1212,1392-1421 -/
def SuccessfulPhasePrefix (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (pref : List Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  ∃ bits : List Bool, bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    pref = bits.take (match BoundedRunPhaseHistory.phaseHistory r o₁ o₂
      (fun i => (bits[i]?).getD false) s j with
      | none => 0
      | some current => current.bitCursor)

end CountingMatroid.Analysis.PhaseObservationExperiment

end


