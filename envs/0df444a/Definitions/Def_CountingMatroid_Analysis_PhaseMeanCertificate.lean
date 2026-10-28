-- Prove2me | Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
-- name    : CountingMatroid_Analysis_PhaseMeanCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:33.534572+00:00
-- url     : https://prove2.me/theorems/4742cd6b-6ab1-438a-b625-2f059efb7055
-- title:
--   Raw empirical-mean certificate for an executed phase
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be Boolean query functions on subsets of $[n]=\{0,\ldots,n-1\}$. Put $E=[n]\times\{0,1\}$, let paired states be subsets of $E$, and write $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ using truncated natural subtraction. A transversal has one label in each pair; a defect $(i,k)$ has empty pair $i$, full pair $k$, and one label elsewhere, with $i\ne k$. Fix a tape, schedule $s$ with factor $\rho$, tolerance $\eta$, and observation count $N$, and phase index $j$. The raw-phase-means predicate requires an actually reached annealing cursor $v$, a successful restart from its tables and bit position, and successful observations at parameter $\rho^j$ using its current weights. It also requires $N>0$ and goodness of $v$: all stored weights through level $j$, and current weights at $j$, lie between one quarter and four times the respective transversal/defect partition ratios.
--   Let $\pi$ denote the normalized operational weights at $\rho^j$ and the current multipliers. Let $\mu_0$ be its transversal indicator mean, $\mu_{ik}$ its distinct-defect indicator means, and $\mu_U$ the mean of $\rho^{d(S)}$ on transversals and zero elsewhere. If the observed type counts are $c_0,c_{ik}$ and the numerator sum is $U$, the predicate requires
--   $$\operatorname{Rel}_\eta(\mu_0,c_0/N),\qquad
--   \operatorname{Rel}_\eta(\mu_U,U/N),\qquad
--   \forall i\ne k,\ \operatorname{Rel}_\eta(\mu_{ik},c_{ik}/N),$$
--   where
--   $$\operatorname{Rel}_\eta(\mu,z)\Longleftrightarrow(1-\eta)\mu\le z\le(1+\eta)\mu.$$
--   The reference means are the fixed operational weighted-sum quotients, not existentially chosen targets. This defines a successful execution-and-estimation predicate; it supplies no probability bound or independent-sample claim.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseMeanCertificate.lean#L24-L49

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

/-!
The raw phase boundary requires relative empirical errors about the normalized
operational state weights. `StationaryMeanIdentities` supplies their exact
type and annealing-observable mean identities using the classifier's
transversal reindexing. Positivity of the true ratio and drift of the ideal
multipliers are deterministic consequences of the concrete schedule and
partition sums, proved in `AnnealingPartitionDrift`. They need not be included
in an event whose probability is estimated. No stochastic estimate is asserted
by this module.
-/

namespace CountingMatroid.Analysis.PhaseMeanCertificate

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: The actual phase's restart and empirical mean estimates,
retaining its good prior history. Means are fixed by the actual normalized
state weights, rather than chosen existentially. Mean identities, positivity,
and ideal-multiplier drift are deterministic facts supplied by the bridge.
TEXLINE: main.tex:1141-1145,1207-1270 -/
def RawPhaseMeans {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  ∃ current : AnnealingCursor n, ∃ start : PairedSet n × ℕ,
    ∃ observed : ObservationCursor n,
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
    FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
    (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val = some start ∧
    (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val =
      some observed ∧
    0 < s.observations ∧
      RelativeEstimate s.η
        (typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights .transversal)
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) ∧
      RelativeEstimate s.η
        (numeratorMean r o₁ o₂ (s.ρ ^ j) s.ρ current.currentWeights)
        (observed.numeratorSum / (s.observations : ℚ)) ∧
      ∀ index : DefectIndex n, RelativeEstimate s.η
        (typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights
          (.defect index.emptyPair index.fullPair))
          ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
            (s.observations : ℚ))



end CountingMatroid.Analysis.PhaseMeanCertificate

end


