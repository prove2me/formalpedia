-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ObservationRoundDrawSites
-- name    : CountingMatroid_Analysis_ObservationRoundDrawSites
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:12:13.340964+00:00
-- url     : https://prove2.me/theorems/416b9aa3-42ab-48ee-9f9b-de5db008871c
-- title:
--   Reached observation failures and their draw sites
-- statement:
--   Fix natural numbers $n,r,j,k$, Boolean subset oracles $o_1,o_2$, input parameters $p$, a Boolean prefix $u$, and a Boolean suffix $v$. Let $s=\operatorname{setup}(n,p)$ and let the tape be $u\mathbin{+\!\!+}v$, defaulted to false beyond its length. The reached-abort predicate requires certificates for all phases $a<j$, an actually reached phase cursor, a successful restart from that cursor, and
--   $$
--   \operatorname{observe}_{k}(\mathrm{start})=\operatorname{some}(z),
--   \qquad
--   \operatorname{observe}_{k+1}(\mathrm{start})=\operatorname{none}
--   $$
--   for some observation cursor $z$. Here only the schedule's observation-count field is changed; both runs use activity $s.\rho^j$ and the reached cursor's current weights.
--
--   For a draw index $b\in\{0,1,2\}$, $\operatorname{observationDrawSite}$ follows the actual phase history, restart, and $k$-observation prefix. It returns no descriptor if any of those operations aborts or if $k=0$; otherwise it applies the chain-draw-site function at the reached state and bit cursor with index $b$. A present result is an absolute cursor and denominator. The predicate and descriptor are definitions and do not assume exact oracles or assert a probabilistic bound.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ObservationRoundDrawSites.lean#L27-L47

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

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
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
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
section


set_option autoImplicit false

/-!
The three stopped draw descriptors of one actual observation attempt. Each
descriptor records an absolute bit cursor and the actual draw denominator.
History, restart, and observation replay compose with the chain-level
stopped-draw replay and abort-attribution invariants. The independent
selector correctness proof is isolated in a child module; trial coverage remains
a separate quantitative obligation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: One reached failing round of the actual observation loop,
retaining the successful phase history, restart, and shorter observation
prefix on the same defaulted finite tape. Changing only `observations`
truncates the loop and leaves every transition parameter unchanged.
TEXLINE: main.tex:1177-1187,1392-1421 -/
def ReachedObservationRoundAbort (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (pref : List Bool) (k : ℕ)
    (suffix : List Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let tape := fun i => ((pref ++ suffix)[i]?).getD false
  (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s a) ∧
  ∃ current : AnnealingCursor n,
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
    ∃ start,
      (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val =
        some start ∧
      ∃ reached : ObservationCursor n,
        (observePhase r o₁ o₂ tape {s with observations := k}
          (s.ρ ^ j) current.currentWeights start).val = some reached ∧
        (observePhase r o₁ o₂ tape {s with observations := k + 1}
          (s.ρ ^ j) current.currentWeights start).val = none

end CountingMatroid.Analysis.ObservationRoundDrawCover

namespace CountingMatroid.Analysis.ObservationRoundDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawCover

/-- INTERNAL: Compose the stopped draw with the actual successful phase
history, restart, and k-observation prefix, all on the given finite tape.
TEXLINE: main.tex:1177-1187,1392-1421 -/
noncomputable def observationDrawSite (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (pref : List Bool) (k : ℕ) (site : Fin 3) (suffix : List Bool) :
    Option (ℕ × ℕ) := do
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let tape := fun i => ((pref ++ suffix)[i]?).getD false
  let current ← BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j
  let start ← (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val
  let reached ← (observePhase r o₁ o₂ tape {s with observations := k}
    (s.ρ ^ j) current.currentWeights start).val
  if k = 0 then none else
    chainDrawSite r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights
      reached.state reached.bitCursor site















end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · proved · closed observation_round_draw_sites with proved stopped-draw replay, sampler range, classifier weight, and selector correctness helpers; preserved the statement and every original import. Both live handoffs were mechanically rejected without diagnostic, so all child proofs were completed vertically.
* r28 · narrowed · after mechanical rejection of r28-observation-draw-sites-1 without diagnostic, proved the chain replay and abort-attribution children; isolated the remaining classifier-valid selection population/count bridge in ClassifiedStateSelection.
* r28 · composed · removed the parent’s local proof gaps by composing history, restart, observation and stopped-chain replay; attributed reached aborts using the independent chain abort helper. Both child statements elaborate; their chain-level proofs are prepared for the live OPEN handoff.
* r27 · decomposed · defined the three pre-draw stopping descriptors; attempted prefix replay and abort attribution, exposing the n-element-state/selection and stopping-locality obligations separately from trial coverage.
-/

end


