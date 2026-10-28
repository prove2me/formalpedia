-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
-- name    : CountingMatroid_Analysis_ExchangeFlowEnergy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:23:28.67556+00:00
-- url     : https://prove2.me/theorems/af09fedd-e19a-4810-90af-c4a3a1097478
-- title:
--   Exchange-flow energies and divergence certificates
-- statement:
--   On a finite vertex set $V$, let $J:V^2\to\mathbb R$ be a current, let $\kappa:V^2\to\mathbb R$ be a conductance function, and let $H:V\to\mathbb R$ be a potential. Define
--   $$
--   \operatorname{div}J(x)=\sum_yJ(x,y),\qquad
--   \mathcal E_\kappa(J)=\frac12\sum_{x,y}\frac{J(x,y)^2}{\kappa(x,y)},\qquad
--   \mathcal E_\kappa(H)=\frac12\sum_{x,y}\kappa(x,y)(H(x)-H(y))^2.
--   $$
--   These formulas are defined without sign or symmetry assumptions and use totalized real division. A flow certificate for a demand $d:V\to\mathbb R$ supplies a current satisfying $J(x,y)=-J(y,x)$, $J(x,y)=0$ whenever $\kappa(x,y)=0$, and $\operatorname{div}J=d$.
--
--   For a probability distribution $\pi$ on paired states, an operational classifier value $a$, and an event $A$ consisting of paired states, the conditional-mean demand is
--   $$
--   d(S)=
--   \mathbf1_{\{\operatorname{classify}(S)=a\}}
--   \frac{\pi(S)}{\sum_{\operatorname{classify}(T)=a}\pi(T)}
--   -
--   \mathbf1_{\{S\in A\}}\frac{\pi(S)}{\sum_{T\in A}\pi(T)}.
--   $$
--   Zero denominators are again totalized; the definition does not require either conditioning event to have positive mass.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeFlowEnergy.lean#L20-L23

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
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
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
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
import Mathlib.Algebra.QuadraticDiscriminant
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

namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
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
Signed exchange flows and their energy inequality. Conductances may vanish:
a flow must be zero on those pairs. These facts supply the summation-by-parts
and Cauchy--Schwarz step in the paper's transport construction; they do not
construct the recursively balanced flow or bound its energy.
-/

namespace CountingMatroid.Analysis.ExchangeFlowEnergy

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open Arlib.Probability
open scoped BigOperators

/-- INTERNAL: Net outgoing current of an antisymmetric finite flow.
TEXLINE: main.tex:493-510 -/
noncomputable def divergence {α : Type*} [Fintype α] (J : α → α → ℝ)
    (x : α) : ℝ := ∑ y, J x y

/-- INTERNAL: Energy of an antisymmetric current, counting each unoriented
edge once. Zero conductances are handled by the flow support condition.
TEXLINE: main.tex:502-510 -/
noncomputable def flowEnergy {α : Type*} [Fintype α]
    (κ J : α → α → ℝ) : ℝ := (1 / 2 : ℝ) * ∑ x, ∑ y, (J x y) ^ 2 / κ x y

/-- INTERNAL: Energy of a potential in the same unoriented-edge convention.
TEXLINE: main.tex:478-483 -/
noncomputable def potentialEnergy {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (H : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, κ x y * (H x - H y) ^ 2

/-- INTERNAL: Data needed from the paper's recursively balanced flow.
TEXLINE: main.tex:493-510,670-709 -/
structure FlowCertificate {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (demand : α → ℝ) where
  current : α → α → ℝ
  antisymmetric : ∀ x y, current x y = -current y x
  supported : ∀ x y, κ x y = 0 → current x y = 0
  divergence_eq : ∀ x, divergence current x = demand x









/-- INTERNAL: Unit source in a classifier fiber and unit sink in a finite
event, with the same totalized conditional denominators as the parent.
TEXLINE: main.tex:493-498,868-904 -/
noncomputable def conditionalMeanDemand {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) (A : Finset (PairedSet n)) (state : PairedSet n) : ℝ := by
  classical
  exact (if (classifyState state).val = kind then π state / classMass π kind else 0) -
    (if state ∈ A then π state / eventMass π A else 0)



end CountingMatroid.Analysis.ExchangeFlowEnergy

end


