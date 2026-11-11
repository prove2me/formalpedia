-- Prove2me | Definitions.Def_OAIQ228B002
-- name    : OAIQ228B002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:16:59.333454+00:00
-- url     : https://prove2.me/theorems/5c29a8c7-e258-42c4-abf7-980f7c74cc03
-- title:
--   Definitions bundle OAIQ228B002 of the split of OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 118 definitions, 5 instances and 5 theorems. The definitions and types are `OAI.CriticalPercolation.Corridor.ScaleChoice.e`, `OAI.CriticalPercolation.Corridor.ScaleChoice.eta`, `OAI.CriticalPercolation.Corridor.ScaleChoice.kappa`, `OAI.CriticalPercolation.Corridor.Scheme.Stable`, `OAI.CriticalPercolation.Corridor.Scheme.accepted`, `OAI.CriticalPercolation.Corridor.Scheme.actual`, `OAI.CriticalPercolation.Corridor.Scheme.allGood`, `OAI.CriticalPercolation.Corridor.Scheme.block`, `OAI.CriticalPercolation.Corridor.Scheme.edgeDomain`, `OAI.CriticalPercolation.Corridor.Scheme.enlarged`, `OAI.CriticalPercolation.Corridor.Scheme.incomingHit`, `OAI.CriticalPercolation.Corridor.Scheme.nextHit`, `OAI.CriticalPercolation.Corridor.Scheme.rootEvent`, `OAI.CriticalPercolation.Corridor.Scheme.rule`, `OAI.CriticalPercolation.Corridor.box`, `OAI.CriticalPercolation.Corridor.boxEdges`, `OAI.CriticalPercolation.Corridor.corridorEdges`, `OAI.CriticalPercolation.Corridor.domain`, `OAI.CriticalPercolation.Corridor.endpoints`, `OAI.CriticalPercolation.Corridor.graphBox`, `OAI.CriticalPercolation.Corridor.graphDomain`, `OAI.CriticalPercolation.Corridor.revealed`, `OAI.CriticalPercolation.Corridor.tube`, `OAI.CriticalPercolation.EuclideanEllipse.diskExpand`, `OAI.CriticalPercolation.EuclideanEllipse.diskNormalize`, `OAI.CriticalPercolation.ExactExposure.Consistent`, `OAI.CriticalPercolation.ExactExposure.Sound`, `OAI.CriticalPercolation.ExactExposure.clusterUsers`, `OAI.CriticalPercolation.FiniteClusters.clusterWeight`, `OAI.CriticalPercolation.FiniteClusters.edgeDiscrepancy`, `OAI.CriticalPercolation.FiniteClusters.edgeMass`, `OAI.CriticalPercolation.FiniteClusters.expectedTransport`, `OAI.CriticalPercolation.FiniteClusters.mass`, `OAI.CriticalPercolation.FiniteClusters.rootAbsolute`, `OAI.CriticalPercolation.FiniteClusters.rootDiscrepancy`, `OAI.CriticalPercolation.FiniteClusters.rootSum`, `OAI.CriticalPercolation.FiniteClusters.size`, `OAI.CriticalPercolation.FiniteClusters.small`, `OAI.CriticalPercolation.FiniteClusters.transport`, `OAI.CriticalPercolation.FiniteClusters.truncatedEdgeMass` and 78 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `CriticalPercolation_Criticality_ActualGrowth`, `CriticalPercolation_Criticality_BoundaryCount`, `CriticalPercolation_Criticality_CutInside`, `CriticalPercolation_Criticality_DeleteImageIso`, `CriticalPercolation_Criticality_GrowthProcess`, `CriticalPercolation_Criticality_Leak`, `CriticalPercolation_Criticality_SharpnessPhi`, `CriticalPercolation_Criticality_TwoPoint`, `CriticalPercolation_Criticality_Weight`, `CriticalPercolation_Entropy_AeEvalNe`, `CriticalPercolation_Entropy_MarkedEntropy`, `CriticalPercolation_Entropy_ReverseGuess`, `CriticalPercolation_Entropy_Uniform01`, `CriticalPercolation_Exploration_AncestryForest`, `CriticalPercolation_Exploration_ClosedFresh`, `CriticalPercolation_Exploration_ClosedPivotWeight`, `CriticalPercolation_Exploration_ClusterUsers`, `CriticalPercolation_Exploration_Exhaustive`, `CriticalPercolation_Exploration_GlobalNode`, `CriticalPercolation_Exploration_GrowthHistoryGeometry`, `CriticalPercolation_Exploration_IncidenceIdentity`, `CriticalPercolation_Exploration_IncidenceSearch`, `CriticalPercolation_Exploration_ListScore`, `CriticalPercolation_Exploration_LocalNode`, `CriticalPercolation_Exploration_Node`, `CriticalPercolation_Exploration_PhaseFrontier`, `CriticalPercolation_Exploration_PrefixState`, `CriticalPercolation_Exploration_QueryTree`, `CriticalPercolation_Exploration_Score`, `CriticalPercolation_Exploration_SearchTree`, `CriticalPercolation_Exploration_Select`, `CriticalPercolation_Exploration_State`, `CriticalPercolation_Exploration_TargetSearch`, `CriticalPercolation_Exploration_Users`, `CriticalPercolation_Exploration_Visits`, `CriticalPercolation_Gluing_CorridorGraph`, `CriticalPercolation_Gluing_CorridorScaleChoice`, `CriticalPercolation_Gluing_CorridorSeparation`, `CriticalPercolation_Gluing_StoredPrediction`, `CriticalPercolation_GraphGeometry_EllipseMesh`, `CriticalPercolation_GraphGeometry_Link2`, `CriticalPercolation_Growth_HomogeneousAverage`, `CriticalPercolation_Growth_HomogeneousGrowth`, `CriticalPercolation_Growth_HomogeneousTransport`, `CriticalPercolation_Modular_ClusterMassInfinite`, `CriticalPercolation_Modular_ClusterTransportFinite`, `CriticalPercolation_Modular_ClusterTransportGeometry`, `CriticalPercolation_Modular_ClusterTransportSums`, `CriticalPercolation_Modular_InputMass`, `CriticalPercolation_Modular_OrderMass`, `CriticalPercolation_Modular_WeightedQuery`, `CriticalPercolation_ProductMeasure_Potential`, `CriticalPercolation_ProductMeasure_QueryMartingale`, `CriticalPercolation_ProductMeasure_Variance`.
--
--   **Imports.** It imports the published bundle `Def_CriticalPercolation`; the bundles `OAIQ228B000` and `OAIQ228B001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost`, `OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy`, `OAI.CriticalPercolation.BinaryLaw.selected_moment`, `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary`, `OAI.CriticalPercolation.BondGraph.restriction_quadratic_real_le`, `OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le`, `OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate`, `OAI.CriticalPercolation.IncidenceSearch.compile_terminal`, `OAI.CriticalPercolation.IncidenceSearch.tree_quadratic`, `OAI.CriticalPercolation.LazyDFS.young_phase_score_bound`, `OAI.CriticalPercolation.SearchTree.normalized_centered_bound` and `OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth`; the proofs of `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost`, `OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy`, `OAI.CriticalPercolation.BinaryLaw.selected_moment`, `OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae`, `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction`, `OAI.CriticalPercolation.BondGraph.criticalProbability_pos`, `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient`, `OAI.CriticalPercolation.BondGraph.expected_discrepancy_peakBand_fourth`, `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary`, `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial`, `OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure`, `OAI.CriticalPercolation.BondGraph.restriction_quadratic_real_le`, `OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le`, `OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound`, `OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate`, `OAI.CriticalPercolation.IncidenceSearch.compile_terminal`, `OAI.CriticalPercolation.IncidenceSearch.tree_quadratic`, `OAI.CriticalPercolation.LazyDFS.young_phase_score_bound`, `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable`, `OAI.CriticalPercolation.SearchTree.normalized_centered_bound` and `OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth`.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def potential (w : E → Prop → ℝ) (U R : Set E → Prop) : ℝ :=
  prob w R - (prob w R)^2/prob w U

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def variance (w : E → Prop → ℝ) (F : Set E → Prop) : ℝ :=
  prob w F - (prob w F)^2

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Corridor

def endpoints (e : Edge) : Set Site := {source e,target e}

def box (j h : ℝ) (v : Site) : Set Point := {x |
    |x.1-((v.1 : ℝ)+v.2)|≤j ∧ |x.2-((v.1 : ℝ)-v.2)|≤j+h}

def tube (h : ℝ) (e : Edge) : Set Point := {x |
    (e.1.1 : ℝ)+e.1.2≤x.1 ∧ x.1≤(e.1.1 : ℝ)+e.1.2+1 ∧
    if e.2 then |x.2-(x.1-2*(e.1.2 : ℝ))|≤h
    else |x.2-(2*(e.1.1 : ℝ)-x.1)|≤h}

def domain (j h : ℝ) (e : Edge) : Set Point :=
  box j h (source e)∪box j h (target e)∪tube h e

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

def graphBox (v : Site) : Set V := ξ ⁻¹' box j h v
def graphDomain (e : Edge) : Set V := ξ ⁻¹' domain j h e
def boxEdges (v : Site) : Set E := G.inducedEdges (graphBox ξ j h v)
def corridorEdges (e : Edge) : Set E := G.inducedEdges (graphDomain ξ j h e)

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_GrowthHistoryGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph Boundary

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

def revealed (S : GrowthState) : Set E :=
  boxEdges G ξ j h (0,0)∪⋃ e∈S.seen, corridorEdges G ξ j h e

lemma revealed_mono {S T : GrowthState} (hST : S.seen⊆T.seen) :
    revealed G ξ j h S⊆revealed G ξ j h T := by
  apply Set.union_subset_union_right
  intro b hb
  obtain ⟨e,he,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.mem_iUnion₂.mpr ⟨e,hST he,hb⟩

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_GrowthProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

namespace Scheme
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def block (S : GrowthState) : Set E := revealed P.graph P.coordinate P.j P.h S

def edgeDomain (e : Edge) : Set E := corridorEdges P.graph P.coordinate P.j P.h e

def enlarged (n : ℕ) (S : GrowthState) : Set E := P.block (S.advance n false)

def incomingHit (n : ℕ) (S : GrowthState) : Set (Set E) := P.hit (slotSite n) (P.enlarged n S)

def nextHit (n : ℕ) (S : GrowthState) (b : Bool) : Set (Set E) :=
  P.hit (target (slotSite n,b)) (P.enlarged n S∪P.edgeDomain (slotSite n,b))

def accepted (n : ℕ) (S : GrowthState) : Set (Set E) :=
  (predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
    (P.nextHit n S true) (P.nextHit n S false) P.delta)ᶜ

lemma accepted_measurable (n : ℕ) (S : GrowthState) :
    MeasurableSet[blockSigma (P.enlarged n S)] (P.accepted n S) :=
  (measurableSet_predictionFailure P.parameter (P.enlarged n S) _ _ _
    (P.graph.measurableSet_restrictedSeed _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
    (P.graph.restrictedSeed_measurable _ _ _) P.delta).compl

def rule : DecisionRule E GrowthState where
  initial := GrowthState.initial
  block := P.block
  further := P.enlarged
  contained n S := revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)
  active n S := (incoming n S.good).isSome
  accept := P.accepted
  measurable := P.accepted_measurable
  update := GrowthState.advance
  block_update _ _ _ := rfl

def rootEvent : Set (Set E) := {ω | ∀ b : Bool,
  1-P.delta ≤ (blockProbability P.parameter (P.block GrowthState.initial)
    (P.hit (target ((0,0),b)) (P.block GrowthState.initial∪P.edgeDomain ((0,0),b))) ω).toReal}

end Scheme
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_StoredPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def Stable (n : ℕ) (S : GrowthState) (ω : Set E) : Prop :=
  (∀ v∈S.good, ω∈P.hit v (P.block S)) ∧
  (∀ e : Edge, source e∈S.good → n ≤ gridSlot (target e) →
    1-P.delta ≤ (blockProbability P.parameter (P.block S)
      (P.hit (target e) (P.block S∪P.edgeDomain e)) ω).toReal)

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ActualGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def actual (n : ℕ) (ω : Set E) : GrowthState := P.rule.state n (P.rule.codeOf n ω)

def allGood (ω : Set E) : Set Site := ⋃ n, ((P.actual n ω).good : Set Site)

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_Weight
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness
open FiniteProduct

variable {E A : Type*} [Fintype E]

def probability (p : ℝ) (F : Set E → Prop) : ℝ :=
  expect (fun _ : E => weight p) (fun ω => if F ω then 1 else 0)

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Link2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness

open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

def reachesTarget (o : V) (T : Set V) (ω : Set E) : Prop :=
  o ∈ roots (G.openGraph ω) T

def boundaryReach (R : Set V) (H : SimpleGraph V) (o : V) (e : E) : Prop :=
  ∃ x y, G.ends e = s(x,y) ∧ x ∉ R ∧ y ∈ R ∧ H.Reachable o x

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BoundaryCount
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule2
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {V E : Type*} [Fintype E] (G : BondGraph V E)

def boundaryCount (o : V) (R : Set V) (H : SimpleGraph V) : ℝ :=
  ∑ e, if boundaryReach G R H o e then 1 else 0

def boundaryFlux (p : ℝ) (o : V) (R : Set V) : ℝ :=
  p * expect (fun _ : E => weight p)
    (fun ω => boundaryCount G o R (delete (G.openGraph ω) R))

end CriticalPercolation.Sharpness
end
end CurrentModule2

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_CutInside
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule3
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

def cutInside (S : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ S then (G.ends e).out.1 else (G.ends e).out.2

def cutOutside (S : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ S then (G.ends e).out.2 else (G.ends e).out.1

def IsCut (S : Set V) (e : E) : Prop := cutInside G S e ∈ S ∧ cutOutside G S e ∉ S

def internalIncident (S C : Set V) : Set E :=
  {e | e ∈ G.incidentEdges C ∧ ∀ v ∈ G.ends e, v ∈ S}

def internalCluster (S : Set V) (o : V) (ω : Set E) : Set V :=
  component (delete (G.openGraph ω) Sᶜ) o

end CriticalPercolation.Sharpness
end
end CurrentModule3

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SharpnessPhi
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule6
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*}

variable (G : BondGraph V E)

def phi (p : unitInterval) (o : V) (S : Set V) : ℝ :=
  (p : ℝ) * ∑' e, (G.law p).real
    {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e}

end CriticalPercolation.Sharpness
end
end CurrentModule6

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DeleteImageIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule9
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

noncomputable def deleteImageIso (φ : G.Aut) (ω : Set E) (S : Set V) :
    delete (G.openGraph ω) S ≃g delete (G.openGraph (φ.edge '' ω)) (φ.vertex '' S) where
  toEquiv := φ.vertex
  map_rel_iff' := by
    intro x y
    change ((G.openGraph (φ.edge '' ω)).Adj (φ.vertex x) (φ.vertex y) ∧
      φ.vertex x ∉ φ.vertex '' S ∧ φ.vertex y ∉ φ.vertex '' S) ↔ _
    simp only [BondGraph.Aut.adj_map,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
    rfl

end CriticalPercolation.Sharpness
end
end CurrentModule9

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_Leak
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule4
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype E]

variable (G : BondGraph V E)

def leak (S C : Set V) (e : E) (v : V) (ω : Set E) : ℝ :=
  if IsCut G S e ∧ cutInside G S e ∈ C then
    if e ∈ ω ∧ (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v then 1 else 0
  else 0

end CriticalPercolation.Sharpness
end
end CurrentModule4

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_TwoPoint
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule10
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

def twoPoint (p : unitInterval) (o v : V) : ℝ := (G.law p).real (G.hitEvent o {v})

end CriticalPercolation.Sharpness
end
end CurrentModule10

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_Uniform01
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

variable {I : Type*} [Fintype I]

noncomputable def law : Measure (I → ℝ) := Measure.pi fun _ => uniform01

instance instIsProbabilityMeasureForallRealLaw : IsProbabilityMeasure (law (I := I)) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_AeEvalNe
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

instance instNullSingletonClassRealUniform01 : NullSingletonClass uniform01 := by
  unfold uniform01
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CriticalPercolation.Priority

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_MarkedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z I M : Type*} [Fintype X] [Fintype Y] [Fintype Z]

noncomputable def conditionalMass (P : X → ℝ) (u : X → Y) (v : X → Z)
    (y : Y) (z : Z) : ℝ :=
  pushMass (fun x => (u x,v x)) P (y,z) / pushMass u P y

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SearchTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

namespace SearchTree
variable {E R : Type*}
def run : SearchTree E R → (E → Bool) → R
  | .done r, _ => r
  | .ask e l r, ω => if ω e then run r ω else run l ω

def reads : SearchTree E R → (E → Bool) → List E
  | .done _, _ => []
  | .ask e l r, ω => e :: if ω e then reads r ω else reads l ω

def Valid [DecidableEq E] : SearchTree E R → Finset E → Prop
  | .done _, _ => True
  | .ask e l r, used => e ∉ used ∧ l.Valid (insert e used) ∧ r.Valid (insert e used)

end SearchTree

end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Exhaustive
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def Exhaustive (G : BondGraph V E) (order : List (Dart V E)) : Prop :=
  ∀ v e t, G.ends e = s(v,t) → (v,e,t) ∈ order

def Frontier (G : BondGraph V E) (st : State V E) (stack : List (Dart V E)) : Prop :=
  ∀ v ∈ st.reached, ∀ e t, G.ends e = s(v,t) → t ∉ st.reached →
    e ∈ st.read ∨ (v,e,t) ∈ stack

def ReadConsistent (G : BondGraph V E) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ e ∈ st.read, ω e = true → ∀ v ∈ G.ends e, v ∈ st.reached

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

noncomputable def score (p : ℝ) (F : Set E → Prop) :
    SearchTree E R → (E → Prop → ℝ) → Set E → ℝ
  | .done _, _, _ => 0
  | .ask e l r, w, ω =>
      (if openPivot F e ω then (1-p)*delta w F e else 0) +
      if ω e then score p F r (pin w e True) ω else score p F l (pin w e False) ω

noncomputable def PhaseAdmissible {V : Type*} (G : BondGraph V E) (s : V) (p : ℝ) :
    SearchTree E R → (E → Prop → ℝ) → Prop
  | .done _, _ => True
  | .ask e l r, w =>
      w e False = 1-p ∧ w e True = p ∧
      (∃ v b, G.ends e = s(v,b) ∧
        ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) ∧
      PhaseAdmissible G s p l (pin w e False) ∧
      PhaseAdmissible G s p r (pin w e True)

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def SupportedTails (G : BondGraph V E) (s : V) (w : E → Prop → ℝ)
    (stack : List (Dart V E)) : Prop :=
  ∀ d ∈ stack, ∀ ω, density w ω ≠ 0 → (G.openGraph ω).Reachable s d.1

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ListScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

noncomputable def listScore (p : ℝ) (F : Set E → Prop) (ω : Set E) :
    List E → (E → Prop → ℝ) → ℝ
  | [], _ => 0
  | e::es, w => (if openPivot F e ω then (1-p)*delta w F e else 0) +
      listScore p F ω es (pin w e (ω e))

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_PhaseFrontier
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def PhaseFrontier (G : BondGraph V E) (A : Set V) (st : State V E)
    (stack : List (Dart V E)) : Prop :=
  ∀ v ∈ st.reached, v ∉ A → ∀ e t, G.ends e = s(v,t) → t ∉ st.reached →
    e ∈ st.read ∨ (v,e,t) ∈ stack

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_PrefixState
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def PrefixState (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) : Prop :=
  a ∈ st.reached ∧ ∀ ω : Set E, density w ω ≠ 0 →
    (∀ v ∈ st.reached, (G.openGraph {e | e ∈ st.read ∧ e ∈ ω}).Reachable a v) ∧
    ReadConsistent G st (fun e => decide (ω e))

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_TargetSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def targetSearch (G : BondGraph V E) (B : Set V)
    (order : List (Dart (Option V) E)) (a : V) : SearchTree E (State (Option V) E) :=
  search (G.wireTargets B) order (collapseTarget B a) {none}

def GoodDarts (G : BondGraph V E) (ds : List (Dart V E)) : Prop :=
  ∀ d ∈ ds, G.ends d.2.1 = s(d.1,d.2.2)

noncomputable def mapDart (B : Set V) (d : Dart V E) : Dart (Option V) E :=
  (collapseTarget B d.1,d.2.1,collapseTarget B d.2.2)
noncomputable def mapState (B : Set V) (st : State V E) : State (Option V) E :=
  ⟨st.reached.image (collapseTarget B),st.read⟩

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def terminalProbability (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => prob w F
  | .ask e l r => if ω e then r.terminalProbability F (pin w e True) ω
      else l.terminalProbability F (pin w e False) ω

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedPivotWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def closedPivotWeight (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  if ¬ω e ∧ openPivot F e (Function.update ω e True) then p*T.queryDelta F w ω e else 0

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_ReverseGuess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def reverseMass (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    b/(1+s+b)^2 + if ω f then r.reverseMass p F (pin w f True) ω (s+b)
      else l.reverseMass p F (pin w f False) ω (s+b)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_AncestryForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

namespace Forest
variable (F : Forest)

def root (F : Forest) (n : ℕ) : ℕ :=
  if _h : n < 2 then n else F.root (F.parent n)
termination_by n
decreasing_by exact F.parent_lt n (by omega)

end Forest
end CriticalPercolation.InterpolationForest

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryTree
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation
open FiniteEntropy

universe u

namespace QueryTree
variable {E : Type u}

instance leafFintype : (t : QueryTree E) → Fintype t.Leaf
  | .stop => inferInstanceAs (Fintype PUnit)
  | .ask _ left right => @instFintypeSum _ _ left.leafFintype right.leafFintype

def reads : (t : QueryTree E) → (E → Bool) → List E
  | .stop, _ => []
  | .ask e left right, ω => e :: if ω e then right.reads ω else left.reads ω

def Valid [DecidableEq E] : QueryTree E → Finset E → Prop
  | .stop, _ => True
  | .ask e left right, used => e ∉ used ∧ left.Valid (insert e used) ∧ right.Valid (insert e used)

noncomputable def reference (p : ℝ) : (t : QueryTree E) → t.Leaf → ℝ
  | .stop, _ => 1
  | .ask _ left _, Sum.inl x => (1-p)*left.reference p x
  | .ask _ _ right, Sum.inr x => p*right.reference p x

noncomputable def charge (F : ℝ → ℝ) : (t : QueryTree E) → (t.Leaf → ℝ) → ℝ
  | .stop, _ => 0
  | .ask _ left right, P =>
      let l := ∑ x, P (Sum.inl x)
      let r := ∑ x, P (Sum.inr x)
      (l+r)*F (r/(l+r)) + left.charge F (fun x => P (Sum.inl x)) +
        right.charge F (fun x => P (Sum.inr x))

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Node
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
variable {E : Type*}

instance nodeFintype : (t : QueryTree E) → Fintype t.Node
  | .stop => inferInstanceAs (Fintype PEmpty)
  | .ask _ l r => @instFintypeSum _ _ (inferInstanceAs (Fintype PUnit))
      (@instFintypeSum _ _ l.nodeFintype r.nodeFintype)

def bit : (t : QueryTree E) → t.Node → E
  | .stop, n => PEmpty.elim n
  | .ask e _ _, .inl _ => e
  | .ask _ l _, .inr (.inl n) => l.bit n
  | .ask _ _ r, .inr (.inr n) => r.bit n

def response : (t : QueryTree E) → t.Node → t.Leaf → Option Bool
  | .stop, n, _ => PEmpty.elim n
  | .ask _ _ _, .inl _, .inl _ => some false
  | .ask _ _ _, .inl _, .inr _ => some true
  | .ask _ l _, .inr (.inl n), .inl x => l.response n x
  | .ask _ _ _, .inr (.inl _), .inr _ => none
  | .ask _ _ _, .inr (.inr _), .inl _ => none
  | .ask _ _ r, .inr (.inr n), .inr x => r.response n x

noncomputable def nodeMass (t : QueryTree E) (P : t.Leaf → ℝ) (n : t.Node) : ℝ :=
  ∑ x, if (t.response n x).isSome then P x else 0

noncomputable def nodeTrueMass (t : QueryTree E) (P : t.Leaf → ℝ) (n : t.Node) : ℝ :=
  ∑ x, if t.response n x = some true then P x else 0

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Visits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*}

def visits (t : QueryTree E) (n : t.Node) (ω : E → Bool) : Bool :=
  (t.response n (t.run ω)).isSome

end CriticalPercolation.QueryTree

namespace CriticalPercolation
universe u v w

namespace MarkedTree
variable {E : Type u} {A : Type v} {B : Type w}

def bare : MarkedTree E A → QueryTree E
  | .stop => .stop
  | .ask e _ l r => .ask e l.bare r.bare

def nodeLabel : (t : MarkedTree E A) → t.bare.Node → A
  | .stop, n => PEmpty.elim n
  | .ask _ a _ _, .inl _ => a
  | .ask _ _ l _, .inr (.inl n) => l.nodeLabel n
  | .ask _ _ _ r, .inr (.inr n) => r.nodeLabel n

def map (f : A → B) : MarkedTree E A → MarkedTree E B
  | .stop => .stop
  | .ask e a l r => .ask e (f a) (l.map f) (r.map f)

end MarkedTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Select
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
variable {E : Type*}

def pathNodes : (t : QueryTree E) → (E → Bool) → List t.Node
  | .stop, _ => []
  | .ask e l r, ω => .inl PUnit.unit ::
      if ω e then (r.pathNodes ω).map (Sum.inr ∘ Sum.inr)
      else (l.pathNodes ω).map (Sum.inr ∘ Sum.inl)

def marked : (t : QueryTree E) → MarkedTree E t.Node
  | .stop => .stop
  | .ask e l r => .ask e (.inl PUnit.unit)
      (l.marked.map (Sum.inr ∘ Sum.inl)) (r.marked.map (Sum.inr ∘ Sum.inr))

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_LocalNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree

variable {E I : Type*} (t : I → QueryTree E)

abbrev LocalNode := (i : I) × (t i).Node

def coord (a : LocalNode t) : E := (t a.1).bit a.2

def algorithm (i : I) : MarkedTree E (LocalNode t) :=
  (t i).marked.map (Sigma.mk i)

def raw (order : List I) : MarkedTree E (LocalNode t) :=
  sequence (order.map (algorithm t))

variable [DecidableEq E] [Fintype E]
def combined (order : List I) : MarkedTree E (LocalNode t) :=
  (raw t order).cached (fun _ => none)

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_OrderMass
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
open FiniteEntropy

variable {I : Type*} [Fintype I]

noncomputable def orderMass (o : Order I) : ℝ := ∫ _u in cell o, (1:ℝ) ∂law
noncomputable def orderWeight (o : Order I) (i : I) : ℝ :=
  ∫ u in cell o, endpointKernel (u i) ∂law
noncomputable def orderSquare (o : Order I) (i : I) : ℝ :=
  ∫ u in cell o, (endpointKernel (u i))^2 ∂law

end CriticalPercolation.Priority

open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Users
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy

variable {E I : Type*} [Fintype I]

noncomputable instance (priority := 2000) localNodeDecidable (t : I → QueryTree E) :
    DecidableEq (LocalNode t) := Classical.decEq _

noncomputable def users (t : I → QueryTree E) (ω : E → Bool) (e : E) : Finset I :=
  Finset.univ.filter (fun i => e ∈ (t i).reads ω)

noncomputable def otherUsers (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E) :
    Finset {j : I // j ≠ i} := (users t ω e).subtype (fun j => j ≠ i)

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_InputMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*} [Fintype E]

noncomputable def inputMass (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) : ℝ :=
  t.nodeMass (pushMass t.run P) n
noncomputable def inputNumerator (t : QueryTree E) (p : ℝ) (P : (E → Bool) → ℝ)
    (n : t.Node) : ℝ := t.nodeTrueMass (pushMass t.run P) n - p*t.inputMass P n

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_GlobalNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy FiniteProduct

variable {E I : Type*} [Fintype E] [Fintype I]

abbrev GlobalNode (t : I → QueryTree E) := (o : Order I) × (combined t o.val).bare.Node

noncomputable abbrev globalTag (t : I → QueryTree E) (x : GlobalNode t) : LocalNode t :=
  (combined t x.1.val).nodeLabel x.2

end CriticalPercolation.OrderedQuery

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_State
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def Consistent (G : BondGraph V E) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ e ∈ st.read, ω e = true → ∀ v ∈ G.ends e, v ∈ st.reached

def Sound (G : BondGraph V E) (S : Set V) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ v ∈ st.reached, ∃ s ∈ S, (G.openGraph {e | ω e = true}).Reachable s v

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteEntropy FiniteProduct

variable {V E I : Type*} [Fintype E] [Fintype I]

noncomputable def clusterUsers (G : BondGraph V E) (a b : I → V) (ω : E → Bool)
    (v : V) : Finset I :=
  Finset.univ.filter (fun i => (G.openGraph {e | ω e = true}).Reachable (a i) v ∨
    (G.openGraph {e | ω e = true}).Reachable (b i) v)

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

 def Available (G : BondGraph V E) (v : V) (st : State E) (e : E) : Prop :=
  e ∉ st.read ∧ e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v)

 def compile (G : BondGraph V E) (v : V) : ℕ → State E → SearchTree E (State E)
  | 0, st => .done st
  | n+1, st => if h : ∃ e, Available G v st e then
      let e := h.choose
      .ask e (compile G v n (st.closed e)) (compile G v n (st.open e))
    else .done st

 def Good (G : BondGraph V E) (v : V) (ω : Set E) (st : State E) : Prop :=
  st.opened ⊆ st.read ∧
  (∀ e ∈ st.read, e ∈ st.opened ↔ e ∈ ω) ∧
  ∀ e ∈ st.read, e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v)

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_QueryMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

def queryCount : SearchTree E R → (E → Prop) → ℕ
  | .done _, _ => 0
  | .ask e l r, ω => 1 + if ω e then queryCount r ω else queryCount l ω

def centeredSum (p : ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then (1-p)+centeredSum p r ω else -p+centeredSum p l ω

def truncate : SearchTree E R → ℕ → SearchTree E Unit
  | _, 0 => .done ()
  | .done _, _+1 => .done ()
  | .ask e l r, n+1 => .ask e (truncate l n) (truncate r n)

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

variable [Fintype E]
 def tree (G : BondGraph V E) (v : V) : SearchTree E (State E) :=
  compile G v (Fintype.card E + 1) ⟨∅,∅⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorScaleChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Classical

namespace CriticalPercolation.Corridor.ScaleChoice

def kappa : ℝ := epsilon*delta/(8*(L+1))
def e : ℝ := 1/(200*(L+3))
def eta : ℝ := kappa^2/(32*(Real.log (4/kappa)+1))

end CriticalPercolation.Corridor.ScaleChoice
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_EllipseMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

def diskNormalize (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  normalize (diskRadius W U p) W (Circle.exp p.2)

def diskExpand (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  expand (diskRadius W U p) W (Circle.exp p.2)

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]
open ActionOrbitTransport

lemma pair_fiber_eq_suborbit (x y : X) :
    {w : X | pairOrbit G X x w=pairOrbit G X x y}=stabilizerOrbit G X x y := by
  ext w
  simp only [Set.mem_ofPred_eq]
  rw [eq_comm,pairOrbit_eq,mem_stabilizerOrbit]

variable (ht : ∀ x y : X, ∃ g : G, g • x=y)
  (hf : ∀ x y : X, (stabilizerOrbit G X x y).Finite)
  (hu : ∀ x y : X, suborbitCard G X x y=suborbitCard G X y x)

include ht hf in
lemma pair_row_finite (o b x : X) :
    {y : X | pairOrbit G X x y=pairOrbit G X o b}.Finite := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←smul_pairOrbit G X g o b]
  simpa only [pair_fiber_eq_suborbit] using hf (g • o) (g • b)

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

lemma suborbit_finite (x y : X) : (stabilizerOrbit W.Aut X x y).Finite := by
  obtain ⟨p,_,_⟩ := W.connected.exists_path_of_dist x y
  apply (W.around x p.length).finite_toSet.subset
  intro z hz
  obtain ⟨g,hgx,rfl⟩ := (mem_stabilizerOrbit W.Aut X).mp hz
  change g x=x at hgx
  change g y∈W.around x p.length
  apply W.mem_around.mpr
  simpa only [hgx] using GraphTopology.iso_reachBall W.graph g (show y∈GraphTopology.reachBall W.graph x p.length from ⟨p,le_rfl⟩)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_HomogeneousGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

def ratio (x y : X) : ℝ := (suborbitCard W.Aut X x y : ℝ)/(suborbitCard W.Aut X y x : ℝ)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassInfinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def size (ω : Set E) (v : V) : ℕ := (G.cluster ω v).ncard

def mass (s : ℕ) (ω : Set E) (v : V) : ℝ := cappedMass s (size G ω v) / size G ω v

def rootSum (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑' e, if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0

def rootDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  mass G s ω v * rootSum G p ω v

def rootAbsolute (s : ℕ) (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  mass G s ω v * |rootSum G p ω v|

def edgeMass (s : ℕ) (ω : Set E) (e : E) : ℝ :=
  cappedMass s (size G ω (G.ends e).out.1) +
    if (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 then 0
    else cappedMass s (size G ω (G.ends e).out.2)

def edgeDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  coefficient p ω e * edgeMass G s ω e

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def small (r : ℕ) (ω : Set E) (v : V) : Prop :=
  ∀ x ∈ G.cluster ω v, ∀ y ∈ G.cluster ω v, y ∈ G.vertexBall x r

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportSums
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def weight (r s : ℕ) (ω : Set E) (v : V) : ℝ :=
  if small G r ω v then mass G s ω v else 0

def transport (r s : ℕ) (p : ℝ) (ω : Set E) (v : V) (e : E) : ℝ :=
  if e ∈ G.incidentEdges (G.cluster ω v) then weight G r s ω v * coefficient p ω e else 0

def clusterWeight (r s : ℕ) (ω : Set E) (v : V) : ℝ :=
  if small G r ω v then cappedMass s (size G ω v) else 0

def truncatedEdgeMass (r s : ℕ) (ω : Set E) (e : E) : ℝ :=
  clusterWeight G r s ω (G.ends e).out.1 +
    if (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 then 0
    else clusterWeight G r s ω (G.ends e).out.2

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportFinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]

def expectedTransport (r s : ℕ) (p : unitInterval) (u : V) (e : E) : ℝ :=
  ∫ ω, transport G r s p ω u e ∂G.law p

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.SearchTree
open FiniteProduct

variable {E R : Type*}

def weightedSum (a : E → ℝ) (p : ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then a e*(1-p)+weightedSum a p r ω
      else -a e*p+weightedSum a p l ω

def quadraticCost (a : E → ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => (a e)^2 + if ω e then quadraticCost a r ω else quadraticCost a l ω

def takeQuadratic (a : E → ℝ) : SearchTree E R → ℝ → SearchTree E Unit
  | .done _, _ => .done ()
  | .ask e l r, B => if (a e)^2 ≤ B then
      .ask e (takeQuadratic a l (B-(a e)^2)) (takeQuadratic a r (B-(a e)^2))
      else .done ()

end CriticalPercolation.SearchTree
end
end

end OAI
end


