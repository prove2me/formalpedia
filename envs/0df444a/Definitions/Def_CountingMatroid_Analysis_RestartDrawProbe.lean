-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
-- name    : CountingMatroid_Analysis_RestartDrawProbe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:20:59.078724+00:00
-- url     : https://prove2.me/theorems/157f8bad-1e23-4fb1-8b07-2c994723a1b6
-- title:
--   Recording an ordinal draw during a counted restart
-- statement:
--   Fix natural ground and rank parameters $n,r$, Boolean subset oracles, a tape, schedule $s$, activity $q$, and multiplier table $w$. For a selected attempt ordinal $a$ and draw index $b\in\{0,1,2\}$, the body-site function inspects an accumulator consisting of an optional cursor, a completion flag, and an auxiliary count. It returns a chain-draw descriptor only when the flag is false, a cursor is present, its attempts are below $s.\mathrm{restartCap}$, and the auxiliary count equals $a$.
--
--   The probed body keeps the first present descriptor and executes the counted body. A probed return repeats this body up to the restart cap, preserving its count and descriptor on an aborted result. Between returns, failure is absorbing. Stage $i$ reads stored weights at $i+1$, uses activity $s.\rho^{i+1}$, and repeats $s.\tau$ transitions. A probed restart begins with a fresh transversal, zero counts, and no descriptor, then executes $j$ stages from a supplied initial bit cursor.
--
--   For a combined draw index $k\in\{0,\ldots,3s.\mathrm{restartCap}-1\}$, the restart probe extracts the descriptor selected by
--   $$
--   a=\left\lfloor k/3\right\rfloor,\qquad b=k\bmod3.
--   $$
--   A present descriptor consists of an absolute pre-draw cursor and denominator. The separate predicate
--   $$
--   \operatorname{PositiveObservation}(D)
--   \ \Longleftrightarrow\
--   \forall(c,v),\ D=\operatorname{some}(c,v)\Longrightarrow v>0
--   $$
--   states denominator positivity. These constructions do not assume that predicate, finite-tape coverage, or successful termination of every return. They instrument the charged model without specifying a physical bit implementation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartDrawProbe.lean#L60-L73

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
A concrete ordinal pre-draw probe for the counted restart. The probe observes
an allowed chain attempt before its trials and retains its first descriptor,
including when the ensuing attempt aborts. Forgetting the descriptor preserves
both components of the counted restart, not just its public result.
No stopping law, finite-block bound, or abort attribution is asserted here.
-/
namespace CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.ObservationRoundDrawSites





/-- INTERNAL: Inspect exactly the selected ordinal attempt before invoking
its counted body. The retained counter fixes the ordinal even on aborts.
TEXLINE: main.tex:1163-1176,1392-1421 -/
noncomputable def bodySite {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    Option (ℕ × ℕ) :=
  if acc.1.2 then none else
  match acc.1.1 with
  | none => none
  | some current =>
    if current.attempts < s.restartCap ∧ acc.2 = ordinal then
      chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw
    else none

/-- INTERNAL: Sticky pre-draw recording around the original counted body.
Computing a descriptor observes the tape without replacing its randomness. -/
noncomputable def probedBody {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      (Option (((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))) := do
  let observed := acc.2.or (bodySite r o₁ o₂ tape s q w ordinal draw acc.1)
  let next ← countedBody r o₁ o₂ tape s q w acc.1
  pure (next.map (fun result => (result, observed)))



/-- INTERNAL: Run the actual capped return scan while retaining a descriptor. -/
noncomputable def probedReturn {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (observed : Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      ((Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) := do
  let scan ← Arlib.Computation.Charged.repeatWhile
    (fun _ acc => probedBody r o₁ o₂ tape s q w ordinal draw acc) s.restartCap
    (((some start, false), count), observed)
  pure (((if scan.1.1.2 then scan.1.1.1 else none), scan.1.2), scan.2)



/-- INTERNAL: Preserve the absorbing failure state between trace returns. -/
noncomputable def probedTransition {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      ((Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :=
  match acc.1.1 with
  | none => pure acc
  | some current => probedReturn r o₁ o₂ tape s q w ordinal draw current acc.1.2 acc.2



/-- INTERNAL: Observe the same stored kernel throughout a stage. -/
noncomputable def probedStage {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (ordinal : ℕ) (draw : Fin 3) (index : ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      ((Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) := do
  let a ← successor index
  let q ← ratPower s.ρ a
  let w ← learnedWeightRead tables a s.L
  Arlib.Computation.Charged.repeatFor
    (fun _ acc => probedTransition r o₁ o₂ tape s q w ordinal draw acc) s.τ acc



/-- INTERNAL: Probe one ordinal draw in the concrete counted restart.
The first recorded descriptor survives subsequent aborts and stages.
TEXLINE: main.tex:1163-1176,1392-1421 -/
noncomputable def probedRestart {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor ordinal : ℕ) (draw : Fin 3) :
    Arlib.Computation.Charged Op Cell
      ((Option (PairedSet n × ℕ) × ℕ) × Option (ℕ × ℕ)) := do
  let initial ← freshTransversal n tape cursor
  let result ← Arlib.Computation.Charged.repeatFor
    (fun index acc => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
    j ((some ⟨initial.1, initial.2, 0⟩, 0), none)
  pure ((result.1.1.map (fun current => (current.state, current.bitCursor)), result.1.2),
    result.2)



/-- INTERNAL: Absolute pre-draw cursor and denominator at ordinal `3*a+b`.
Unlike a finite suffix descriptor, this definition needs no block bound. -/
noncomputable def restartDrawProbe {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) (k : Fin (3 * s.restartCap)) : Option (ℕ × ℕ) :=
  (probedRestart r o₁ o₂ tape s tables j cursor (k.val / 3)
    ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩).val.2







/-- INTERNAL: Positivity is an observation invariant independent of cursor
coverage and stopping-prefix replay. -/
 def PositiveObservation (observed : Option (ℕ × ℕ)) : Prop :=
  ∀ d, observed = some d → 0 < d.2



end CountingMatroid.Analysis.RestartDrawProbe

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · return scans retain already-captured descriptors independently of later tape; used this latch in denominator positivity.
* 2026-10-09 · proved · concrete sticky ordinal probes preserve the counted body,
  return, transition, stage, and complete restart, including the abort cost.
-/

end


