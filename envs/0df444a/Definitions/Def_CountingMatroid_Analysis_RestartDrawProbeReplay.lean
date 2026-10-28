-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeReplay
-- name    : CountingMatroid_Analysis_RestartDrawProbeReplay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:22:54.285357+00:00
-- url     : https://prove2.me/theorems/d22f6522-960f-4e0b-aeea-f549d05e93f2
-- title:
--   Replay contract for a restart draw-probe step
-- statement:
--   Let $X$ be a state type, let $c:X\to\mathbb N$ assign a bit cursor, and fix a target ordinal $a\in\mathbb N$. A probe transformation $T$ takes a Boolean tape and an accumulator $((x,k),d)$, where $x$ is an optional live state, $k$ a count, and $d$ an optional pair of natural numbers describing a captured draw. The predicate $\operatorname{ProbeStep}(c,a,T)$ imposes five conditions.
--
--   A captured descriptor is sticky: if the input descriptor is $d$, the output descriptor remains $d$. A dead accumulator with no descriptor is unchanged. An uncaptured input with $k>a$ remains uncaptured with output count still greater than $a$.
--
--   For every live input $x$, count $k$, and floor $\ell\leq c(x)$, a successful capture $d=(p,v)$ satisfies $\ell\leq p$ and is reproduced on every tape agreeing with the original on the interval
--   $$[\ell,p)=\{i\in\mathbb N:\ell\leq i<p\}.$$
--   Finally, if the same live input produces $((y,k'),\mathrm{none})$ with $k'\leq a$, then $\ell\leq c(y)$, and agreement on $[\ell,c(y))$ reproduces the entire output accumulator. These are conditional replay obligations; the contract imposes no general count-monotonicity or resource bound.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartDrawProbeReplay.lean#L20-L40

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
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
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
Pre-draw replay for the concrete ordinal probe, independent of schedule
arithmetic, finite-prefix packaging, or probability. The probe's descriptor
depends only on the tape between the restart cursor and the descriptor's own
cursor, even though the counted state continues reading afterwards. The proof
packages a per-step replay contract (`ProbeStep`) — sticky capture, inert
death, silence past the ordinal, capture replay, and quiet whole-value replay
— shows it for one trace transition from the scan lemmas, and closes it under
the transition and stage folds.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartDrawProbe

/-- INTERNAL: The replay contract of one fresh-observation step of the probe
over accumulators `((state, count), observed)`: a captured descriptor is sticky;
a dead state is inert; a step entered past the ordinal never captures; a
capture replays from the entering floor to the descriptor cursor; and a quiet
live step ending at or before the ordinal replays its whole value from the
floor to its own cursor. The contract is closed under folds.
TEXLINE: main.tex:1163-1176,1392-1421 -/
structure ProbeStep {X : Type} (bc : X → ℕ) (ordinal : ℕ)
    (T : (ℕ → Bool) → (Option X × ℕ) × Option (ℕ × ℕ) → (Option X × ℕ) × Option (ℕ × ℕ)) :
    Prop where
  sticky : ∀ tape acc d, acc.2 = some d → (T tape acc).2 = some d
  dead : ∀ tape count, T tape ((none, count), none) = ((none, count), none)
  past : ∀ tape acc, acc.2 = none → ordinal < acc.1.2 →
    (T tape acc).2 = none ∧ ordinal < (T tape acc).1.2
  capture : ∀ cur count floor, floor ≤ bc cur →
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => (T tape ((some cur, count), none)).2) Prod.fst floor
  quiet : ∀ cur count floor, floor ≤ bc cur → ∀ tape c count',
    T tape ((some cur, count), none) = ((some c, count'), none) → count' ≤ ordinal →
    floor ≤ bc c ∧ ∀ other, (∀ i, floor ≤ i → i < bc c → tape i = other i) →
      T other ((some cur, count), none) = ((some c, count'), none)











end CountingMatroid.Analysis.RestartDrawProbeReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · replay contract `ProbeStep` closed under folds; lifted
  the scan-level replay of `RestartDrawProbeScanReplay` to the whole restart.
* 2026-10-09 · open · exposed fixed-probe stage fold; generic absorbing-Option
  replay cannot replay the continuing product to the earlier observed cursor.
-/

end


