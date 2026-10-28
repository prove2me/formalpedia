-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
-- name    : CountingMatroid_Analysis_RestartAttemptAccounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:12:26.700877+00:00
-- url     : https://prove2.me/theorems/e1628ad5-1343-4bc7-abc8-356372b6d329
-- title:
--   Attempt accounting for capped restart scans
-- statement:
--   Fix a ground-set size $n$, a natural rank parameter $r$, Boolean subset oracles $o_1,o_2$, a Boolean tape, a schedule $s$, a rational activity $q$, and a multiplier table $w$. A return-scan accumulator contains an optional restart cursor $u$, a Boolean flag $e$ indicating completion, and an auxiliary natural count $a$. Its attempt increment is
--   $$
--   \Delta(u,e)=
--   \begin{cases}
--   1,&e=\mathrm{false},\ u=\operatorname{some}(v),\
--   v.\mathrm{attempts}<s.\mathrm{restartCap},\\
--   0,&\text{otherwise}.
--   \end{cases}
--   $$
--   The body stops when completion is already recorded or no cursor remains. At the cap it records failure and completion. Otherwise it executes one chain step, counts that attempt even if the draw aborts, and, on success, updates the state and cursor and tests whether the new state is transversal. The counted body attaches $a+\Delta$ to every produced next accumulator.
--
--   A counted return makes at most $\mathrm{restartCap}$ body iterations and yields an endpoint only when the completion flag is set. Failure is absorbing between returns. Stage $i$ uses activity $s.\rho^{i+1}$ and stored weights at $i+1$, repeating $s.\tau$ returns. The counted restart begins with a fresh transversal, zero attempts, and zero auxiliary count, then executes $j$ stages. Its output retains both the optional endpoint and the accumulated attempt count.
--
--   For input parameters $p$, a prefix witness for phase $j$ requires a finite tape of the prescribed block length, certificates for every earlier phase, an actually reached phase cursor with good stored multipliers, and equality of the supplied prefix with the tape truncated at that cursor. For a prefix and a suffix, $\operatorname{prefixAttemptCost}$ is the auxiliary count of the corresponding counted restart, using their concatenation defaulted to false outside its length. Prefix truncation is part of the definition; cursor coverage and probabilistic bounds are separate obligations. All program charges remain abstract model charges.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartAttemptAccounting.lean#L16-L40

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

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
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
Value-preserving restart instrumentation. The auxiliary natural number counts
only calls to `chainStep`; it survives both draw aborts and attempt-cap aborts.
It uses the original charged operations and the original tape. It establishes
no probabilistic bound and constructs no draw histories.
-/
namespace CountingMatroid.Analysis.RestartAttemptAccounting

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The body of the actual positive-time return loop, factored out
without changing any of its guards or abort branches.
TEXLINE: main.tex:1163-1176 -/
def traceBody {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (acc : Option (RestartCursor n) × Bool) :
    Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) := do
  if acc.2 then pure none
  else match acc.1 with
  | none => pure none
  | some current =>
      let allowed ← lessThan current.attempts s.restartCap
      if allowed then
        let attempted ← chainStep r o₁ o₂ tape s.drawTrials q w
          current.state current.bitCursor
        let attempts ← successor current.attempts
        match attempted with
        | none => pure (some (none, true))
        | some (state, bitCursor) =>
            let kind ← classifyState state
            let returned ← match kind with
              | .transversal => pure true
              | _ => pure false
            pure (some (some ⟨state, bitCursor, attempts⟩, returned))
      else pure (some (none, true))

/-- INTERNAL: Exactly one attempt is made when the return-loop guard allows
`chainStep`; neither an absorbing state nor a refused guard spends a token. -/
def attemptIncrement {n : ℕ} (s : AnnealingSchedule)
    (acc : Option (RestartCursor n) × Bool) : ℕ :=
  if acc.2 then 0 else match acc.1 with
  | none => 0
  | some current => if current.attempts < s.restartCap then 1 else 0

/-- INTERNAL: Attach the attempt token to the original return-body result,
including the `some (none, true)` result on a draw abort. -/
def countedBody {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    Arlib.Computation.Charged Op Cell
      (Option ((Option (RestartCursor n) × Bool) × ℕ)) := do
  let next ← traceBody r o₁ o₂ tape s q w acc.1
  pure (next.map (fun result => (result, acc.2 + attemptIncrement s acc.1)))



/-- INTERNAL: A positive-time trace return with its stopped global attempt
count, retained even when the public result is `none`.
TEXLINE: main.tex:1163-1176 -/
def countedReturn {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : RestartCursor n) (count : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n) × ℕ) := do
  let scan ← Arlib.Computation.Charged.repeatWhile
    (fun _ acc => countedBody r o₁ o₂ tape s q w acc) s.restartCap
    ((some start, false), count)
  pure ((if scan.1.2 then scan.1.1 else none), scan.2)







/-- INTERNAL: One instrumented trace transition, preserving the absorbing
abort state and its last attempt count. -/
def countedTransition {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (acc : Option (RestartCursor n) × ℕ) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n) × ℕ) :=
  match acc.1 with
  | none => pure acc
  | some current => countedReturn r o₁ o₂ tape s q w current acc.2

/-- INTERNAL: One stored-parameter stage with retained abort accounting. -/
def countedStage {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (index : ℕ) (acc : Option (RestartCursor n) × ℕ) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n) × ℕ) := do
  let a ← successor index
  let q ← ratPower s.ρ a
  let w ← learnedWeightRead tables a s.L
  Arlib.Computation.Charged.repeatFor
    (fun _ acc => countedTransition r o₁ o₂ tape s q w acc) s.τ acc

/-- INTERNAL: Restart instrumentation with the same fresh transversal, tape,
stored tables, stage order and shared cap as the program.
TEXLINE: main.tex:1163-1176 -/
def countedRestart {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ) × ℕ) := do
  let initial ← freshTransversal n tape cursor
  let result ← Arlib.Computation.Charged.repeatFor
    (fun index acc => countedStage r o₁ o₂ tape s tables index acc)
    j (some ⟨initial.1, initial.2, 0⟩, 0)
  pure (result.1.map (fun current => (current.state, current.bitCursor)), result.2)





/-- INTERNAL: The already-proved actual-history data fixing one restart's
stored kernels and starting bit cursor. This record asserts no moment bound
and no equality between the cursor and the truncated prefix length.
TEXLINE: main.tex:1207-1212 -/
structure RestartPrefixWitness (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (pref : List Bool) where
  bits : List Bool
  current : AnnealingCursor n
  length : bits.length = CountingMatroid.Model.Run.blockLength n r p
  previous : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
    (fun i => (bits[i]?).getD false) (CountingMatroid.Interface.Pseudocode.setup n p) a
  reached : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
    (fun i => (bits[i]?).getD false) (CountingMatroid.Interface.Pseudocode.setup n p) j =
      some current
  good : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
    (CountingMatroid.Interface.Pseudocode.setup n p) j current
  consumed : pref = bits.take current.bitCursor



/-- INTERNAL: The fixed stopped cost for a restart after this actual earlier
history, evaluated on the original finite tape. Draw aborts retain the token
spent on their last attempted transition; no constant cap witness is used.
TEXLINE: main.tex:1230-1239,1392-1421 -/
noncomputable def prefixAttemptCost {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool) : ℕ :=
  (countedRestart r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
    (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
    j history.current.bitCursor).val.2

end CountingMatroid.Analysis.RestartAttemptAccounting

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · instrumented the actual guarded trace body and nested restart; projection preserves every public value, while the independent attempt counter survives abort. Packaged the existing reached-prefix witness.
-/

end


