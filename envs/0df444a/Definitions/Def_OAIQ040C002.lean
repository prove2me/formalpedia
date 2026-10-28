-- Prove2me | Definitions.Def_OAIQ040C002
-- name    : OAIQ040C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T00:44:47.340051+00:00
-- url     : https://prove2.me/theorems/e1e19592-60a9-4785-a210-5634b6823320
-- title:
--   Definitions bundle OAIQ040C002 of the split of OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 157 declarations of OpenAI's Lean: 144 definitions and 13 theorems. The definitions and types are `OAI.Percolation.corridorDerivativeContribution`, `OAI.Percolation.cutCoefficient`, `OAI.Percolation.cutIso`, `OAI.Percolation.cutMomentValue`, `OAI.Percolation.deformedClusterMass`, `OAI.Percolation.deformedDerivativeMass`, `OAI.Percolation.deformedFreshExteriorMoment`, `OAI.Percolation.degree`, `OAI.Percolation.deletedBoundaryPotential`, `OAI.Percolation.deletedLocalPotential`, `OAI.Percolation.deletionContacts`, `OAI.Percolation.derivativeTransportMass`, `OAI.Percolation.diagonalLossMass`, `OAI.Percolation.diagonalLossTerm`, `OAI.Percolation.distinctClusterMoment`, `OAI.Percolation.domainTwoPoint`, `OAI.Percolation.dyadicBinProbability`, `OAI.Percolation.edgeVertices`, `OAI.Percolation.encodeFiniteJoint`, `OAI.Percolation.encounterCount`, `OAI.Percolation.encounters`, `OAI.Percolation.endpointRootMass`, `OAI.Percolation.ennMatrixCoeff`, `OAI.Percolation.escapeLabelProbability`, `OAI.Percolation.escapeLabelRaw`, `OAI.Percolation.escapeLabelTransport`, `OAI.Percolation.exposedVertexPotential`, `OAI.Percolation.exteriorLegProduct`, `OAI.Percolation.exteriorSearchScore`, `OAI.Percolation.fieldLaw`, `OAI.Percolation.finiteBadGoodnessProbability`, `OAI.Percolation.finiteBadPieceProbability`, `OAI.Percolation.finiteBinConnection`, `OAI.Percolation.finiteCappedRadiusTail`, `OAI.Percolation.finiteChoiceHit`, `OAI.Percolation.finiteChoiceSeparatedPairMass`, `OAI.Percolation.finiteClosedContact`, `OAI.Percolation.finiteClusterTail`, `OAI.Percolation.finiteClusterTailIndicator`, `OAI.Percolation.finiteClusterWeight` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/UnimodularPercolation, in whole or in part: `UnimodularPercolation_Cayley_Folner`, `UnimodularPercolation_Clusters_ExteriorMoments`, `UnimodularPercolation_Clusters_KernelMoments`, `UnimodularPercolation_Clusters_LargeContacts`, `UnimodularPercolation_Clusters_Resampling`, `UnimodularPercolation_Criticality_Sharpness`, `UnimodularPercolation_Criticality_Susceptibility`, `UnimodularPercolation_Deformation_AveragedDecrease`, `UnimodularPercolation_Deformation_Calibration`, `UnimodularPercolation_Deformation_ClusterProducts`, `UnimodularPercolation_Deformation_Derivatives`, `UnimodularPercolation_Encounter_Counts`, `UnimodularPercolation_Encounter_IntrinsicDistance`, `UnimodularPercolation_Encounter_NearestMass`, `UnimodularPercolation_Encounter_Vertices`, `UnimodularPercolation_Escape_CollisionTails`, `UnimodularPercolation_Escape_Labels`, `UnimodularPercolation_Escape_PathSelection`, `UnimodularPercolation_Escape_PositiveEscapes`, `UnimodularPercolation_Escape_SelectionBounds`, `UnimodularPercolation_Exploration_FractionalMoments`, `UnimodularPercolation_Exploration_Goodness`, `UnimodularPercolation_Exploration_Marked`, `UnimodularPercolation_Exploration_Moments`, `UnimodularPercolation_Exploration_TailBounds`, `UnimodularPercolation_Graph_Basic`, `UnimodularPercolation_Graph_Paths`, `UnimodularPercolation_Kernel_Amplification`, `UnimodularPercolation_Kernel_ContactTrace`, `UnimodularPercolation_Kernel_Covariance`, `UnimodularPercolation_Kernel_DistinctMoments`, `UnimodularPercolation_Kernel_RussoRows`, `UnimodularPercolation_Kernel_ScaleBudget`, `UnimodularPercolation_Kernel_Spectral`, `UnimodularPercolation_Kernel_Sprinkling`, `UnimodularPercolation_Kernel_TraceBounds`, `UnimodularPercolation_ProductMeasure_Association`, `UnimodularPercolation_Splicing_EndpointMoments`, `UnimodularPercolation_Splicing_GapCodes`, `UnimodularPercolation_Splicing_Geometry`, `UnimodularPercolation_Splicing_MomentBounds`, `UnimodularPercolation_Splicing_ReferenceLaws`, `UnimodularPercolation_Splicing_Replay`, `UnimodularPercolation_Transport_EndpointKernels`, `UnimodularPercolation_Transport_TrajectoryMass`.
--
--   **Imports.** It imports the published bundle `Def_CayleyPercolation`; the bundles `OAIQ040C000` and `OAIQ040C001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower`, `OAI.Percolation.LocalEndpointRule.quantitative_amplification_step`, `OAI.Percolation.almost_linear_susceptibility`, `OAI.Percolation.conditional_first_escape_collision_bound`, `OAI.Percolation.critical_bounded_of_transport_finiteness`, `OAI.Percolation.critical_encounter_zero`, `OAI.Percolation.critical_finite_ae_of_transport`, `OAI.Percolation.critical_large_contact_bound`, `OAI.Percolation.critical_rootTriangle_subpower`, `OAI.Percolation.critical_root_power_integrable`, `OAI.Percolation.critical_unique_probability_zero`, `OAI.Percolation.deformed_root_sum_retained`, `OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment`, `OAI.Percolation.exists_finite_scale_obstruction`, `OAI.Percolation.exists_selected_path_mass`, `OAI.Percolation.exists_uniform_averaged_decrease`, `OAI.Percolation.exists_uniform_deformed_row_comparison`, `OAI.Percolation.raw_derivative_template_row_lower`, `OAI.Percolation.rooted_label_collision_potential_failure_bound` and `OAI.Percolation.rooted_selected_label_mass_lower`; the proofs of `OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower`, `OAI.Percolation.LocalEndpointRule.quantitative_amplification_step`, `OAI.Percolation.almost_linear_susceptibility`, `OAI.Percolation.arbitrary_cayley`, `OAI.Percolation.conditional_first_escape_collision_bound`, `OAI.Percolation.critical_bounded_of_transport_finiteness`, `OAI.Percolation.critical_encounter_zero`, `OAI.Percolation.critical_finite_ae_of_transport`, `OAI.Percolation.critical_large_contact_bound`, `OAI.Percolation.critical_rootTriangle_subpower`, `OAI.Percolation.critical_root_power_integrable`, `OAI.Percolation.critical_unique_probability_zero`, `OAI.Percolation.deformed_root_sum_retained`, `OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment`, `OAI.Percolation.exists_finite_scale_obstruction`, `OAI.Percolation.exists_selected_path_mass`, `OAI.Percolation.exists_uniform_averaged_decrease`, `OAI.Percolation.exists_uniform_deformed_row_comparison`, `OAI.Percolation.infinitely_many_of_pc_lt_lt_pu`, `OAI.Percolation.mainConclusion_of_strict_gap`, `OAI.Percolation.raw_derivative_template_row_lower`, `OAI.Percolation.rooted_label_collision_potential_failure_bound` and `OAI.Percolation.rooted_selected_label_mass_lower`.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/UnimodularPercolation at commit adc7f12

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C000
import Definitions.Def_OAIQ040C001

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}


def vertexBoundary (G : BondGraph V E) (A : Finset V) : Set V :=
  {y | y ∉ A ∧ ∃ x ∈ A, Adj G x y}

 
noncomputable def hV (G : BondGraph V E) : ℝ :=
  sInf {r | ∃ A : Finset V, A.Nonempty ∧
    r = (vertexBoundary G A).ncard / (A.card : ℝ)}


end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteBK
attribute [local instance] Classical.propDecidable

@[simp] theorem empty_mem_disjointOccurrence (A B : Set (Set E)) :
    (∅ : Set E) ∈ DisjointOccurrence A B ↔ ∅ ∈ A ∧ ∅ ∈ B := by
  constructor
  · rintro ⟨s, t, hs, ht, _, ha, hb⟩
    have hse : (s : Set E) = ∅ := Set.subset_empty_iff.mp hs
    have hte : (t : Set E) = ∅ := Set.subset_empty_iff.mp ht
    exact ⟨hse ▸ ha, hte ▸ hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨∅, ∅, by simp, by simp, by simp, by simpa using ha, by simpa using hb⟩



end FiniteBK

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DegreeBound
attribute [local instance] Classical.propDecidable

 noncomputable def stepEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (x : V) : Step G x ≃ Step G (a x) where
  toFun d := ⟨(b d.val.1, a d.val.2), by rw [h, d.property, Sym2.map_mk]⟩
  invFun d := ⟨(b.symm d.val.1, a.symm d.val.2), by
    rw [isAut_symm G h, d.property, Sym2.map_mk, Equiv.symm_apply_apply]⟩
  left_inv d := by apply Subtype.ext; exact Prod.ext (b.symm_apply_apply _) (a.symm_apply_apply _)
  right_inv d := by apply Subtype.ext; exact Prod.ext (b.apply_symm_apply _) (a.apply_symm_apply _)

 noncomputable def degree (G : BondGraph V E) (x : V) : ℕ := Nat.card (Step G x)

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

 theorem reachBall_mono (G : BondGraph V E) (x : V) : Monotone (reachBall G x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

end SmallParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

noncomputable def fieldLaw (p a : unitInterval) : Measure (Bool → Set E) :=
  Measure.infinitePi (fun b => law (pairParameter p a b))

end SprinklingLaw

section FiniteGraphOperators
attribute [local instance] Classical.propDecidable

 noncomputable def edgeVertices [Fintype E] (G : BondGraph V E) : Finset V :=
   Finset.univ.biUnion (fun e => (G e).toFinset)

end FiniteGraphOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def finiteEventPolynomial (s : Finset E) (A : Set (Set E)) (p : ℝ) : ℝ :=
  bernoulliPolynomial s (fun t => if (t : Set E) ∈ A then 1 else 0) p

end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


attribute [local instance] Classical.decEq


noncomputable def regionProbability (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) : ℝ :=
  bernoulliPolynomial F (fun t => if unexposed G Λ (t : Set E) = S then 1 else 0) p

end ExteriorExposure

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def domainTwoPoint (G : BondGraph V E) (S : Set V) (p : unitInterval)
    (x y : V) : ℝ := (law p).real {ω | Conn G (ω ∩ internalEdges G S) x y}

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def queryPotential (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Finset E :=
  Q.filter (fun e => ∃ v ∈ R, v ∈ G e)

noncomputable def searchVertices (G : BondGraph V E) (Q : Finset E) : Finset V :=
  Q.biUnion fun e => (G e).toFinset

noncomputable def markedClusterTree (G : BondGraph V E) (Q : Finset E) (x : V) : LabelledTree V E :=
  .mark x (clusterSearch G Q.card Q {x}) (.done true)

end GraphSearchCost

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def markedConnectionPolynomial (G : BondGraph V E) (Q : Finset E)
    (x : V) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial (insert x (searchVertices G Q))
    (fun m => if ∃ y ∈ m, Conn G (ω : Set E) x y then 1 else 0) h) p


noncomputable def markedPivotalMomentOne (G : BondGraph V E) (Q : Finset E) (x : V)
    (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial (insert x (searchVertices G Q))
    (fun m => ((markedOpenPivotals G Q x ω m).card:ℝ)) h) p

end MarkedFirstMoment

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteMarkedMoment (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (markedMomentValue G Q x i ω) h) p

end MarkedRecursion

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def cutMomentValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if cluster G ω x = (W : Set V) then
    if Disjoint (W : Set V) (m : Set V) then
      markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i
        (exteriorBonds G ω W) (exteriorMarks m W)
    else 0
  else 0

end CutFactor

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def pivotalSuffixValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if OpenMarkedPivotal G ω m x e then
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) else 0


end PointwiseRecursion

section FiniteMomentRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

 
noncomputable def cutCoefficient (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (h p : ℝ) : ℝ :=
  bernoulliPolynomial ((Q.erase e) \ exteriorBonds G Q W)
    (fun a => if cluster G a x = (W : Set V) then (1:ℝ) else 0) p * (1-h)^W.card


end FiniteMomentRecursion

section MarkedExponential
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteMarkedGenerating (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (z h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m =>
    if MarkedEvent G ω m x then (1+z)^(markedOpenPivotals G Q x ω m).card else 0) h) p

noncomputable def finiteMarkedTail (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (r : ℕ) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m =>
    if MarkedEvent G ω m x ∧ r ≤ (markedOpenPivotals G Q x ω m).card then (1:ℝ) else 0) h) p

end MarkedExponential

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Goodness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteCappedRadius
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteCappedRadiusTail (G : BondGraph V E) (Q : Finset E)
    (x : V) (M r : ℕ) (p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if CappedRadiusEvent G Q x M r ω then 1 else 0) p


end FiniteCappedRadius

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def pruneContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) : Finset E :=
  ω.filter fun f => ¬CutExists G W f ∨ f = e

end PruningGeometry

section FiniteGoodnessProbability
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteBadPieceProbability (G : BondGraph V E) (Q : Finset E)
    (x : V) (M K : ℕ) (L p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if BadPieceEvent G Q x M K L ω then 1 else 0) p

noncomputable def finiteBadGoodnessProbability (G : BondGraph V E) (Q : Finset E)
    (x : V) (M : ℕ) (L p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if CappedBadGoodnessEvent G Q x M L ω then 1 else 0) p


end FiniteGoodnessProbability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


noncomputable def neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) : Finset V := S ∪ S.biUnion (neighbors G hloc)

end IsoperimetricEnergy

section SymmetricWalk
attribute [local instance] Classical.propDecidable

 

noncomputable def walkKernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : ℝ :=
  (if x = y then 1 - a * (neighbors G hloc x).card else 0) +
    (if Adj G x y then a else 0)

end SymmetricWalk

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable
local instance spectralNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

 
def vertexAut (G : BondGraph V E) : Set (V ≃ V) := {a | ∃ b : E ≃ E, IsAut G a b}

end InvariantPercolationOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section DeletionGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 
def deletionContacts (G : BondGraph V E) (ω : Set E) (A B : Set V) : Set E :=
  {e | e ∈ ω ∧ ∃ a ∈ B, ∃ b ∈ A, G e = s(a,b)}



end DeletionGoodness

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_GapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def spliceTupleWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) : ℝ :=
  bernoulliWeight Q (domainBits Q s.1) p *
    ∏ i ∈ J, bernoulliWeight Q (domainBits Q (s.2 i)) p

end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Replay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq


def patchFirst (U τ : Set E) (s : SpliceState E) : SpliceState E :=
  (exchangeOn U s.1 τ,s.2)

end MaskExecution

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_ReferenceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteJointMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

def jointOutput (G : BondGraph V E) (x : V) (η₁ η₂ : ℕ → Set E)
    (y₁ y₂ : ℕ → V) (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E)) : JointSpliceState E :=
  (ωf,(runMasks (replayMasks G x η₁ y₁ c₁ ω₁) (ω₁,η₁)).2,
    (runMasks (replayMasks G x η₂ y₂ c₂ ω₂) (ω₂,η₂)).2)

def jointRestored (G : BondGraph V E) (x : V) (η₁ η₂ : ℕ → Set E)
    (y₂ : ℕ → V) (ω₁ ω₂ : Set E) (c₂ : List (ℕ × E)) : JointSpliceState E :=
  (exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂,η₁,η₂)



end FiniteJointMass

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallHanging
attribute [local instance] Classical.propDecidable Classical.decEq

 
def hangingSide (G : BondGraph V E) (ω : Set E) (x : V) (e : E) : Set V :=
  cluster G ω x \ cluster G (ω \ {e}) x

theorem hangingSide_finite (G : BondGraph V E) (ω : Set E) (x : V) (e : E)
    (hC : (cluster G ω x).Finite) : (hangingSide G ω x e).Finite := hC.subset Set.sdiff_subset



noncomputable def smallSeparatingBonds (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) : Finset E :=
  (separatingBonds G ω x z).filter fun e => (hangingSide G ω x e).ncard ≤ v

noncomputable def smallHangingThrough (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : Finset V :=
  (smallSeparatingBonds G ω x z v).biUnion fun e => (hangingSide_finite G ω x e hC).toFinset

end SmallHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHanging
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def graphNeighbors (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) : Finset V := A.biUnion (neighbors G hloc)



noncomputable def nearHangingEndpoints (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x z : V) (e : E) (v : ℕ) (hC : (cluster G ω x).Finite) : Finset V :=
  ((hangingSide_finite G ω x e hC).toFinset ∪ smallHangingThrough G ω x z v hC) ∪
    (graphNeighbors G hloc (hangingSide_finite G ω x e hC).toFinset).biUnion
      (fun a => smallHangingThrough G ω x a v hC)

end NearHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq


def encodeFiniteJoint (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s : FiniteJointData Q J₁ J₂) : JointSpliceState E :=
  (finiteFieldSet Q s.1,finiteFieldFamily Q J₁ s.2.1,finiteFieldFamily Q J₂ s.2.2)

end FiniteReferenceLaw

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceFactor
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def finiteJointDomain (Q : Finset E) (J₁ J₂ : Finset ℕ) :
    Finset (JointSpliceState E) := Finset.univ.image (encodeFiniteJoint Q J₁ J₂)

end FiniteReferenceFactor

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]


noncomputable def replaySeedFiber (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) : List (ℕ × E) → Set E → ℕ → Set unitInterval
  | [], _, _ => Set.univ
  | (j,e)::c, ω, i =>
    let S := cluster G ω x
    let B := cluster G (η j ∩ internalEdges G Sᶜ) (y j)
    if i = j then {t | chooseContact (fun _ => t) j (contactSet G (η j) B) = e}
    else replaySeedFiber G x η y c (spliceField G S B e ω (η j)) i

@[simp] theorem finiteContactSeeds_at (k : ℕ) (u : Fin k → unitInterval) (i : Fin k) :
    finiteContactSeeds k u (i.val+1) = u i := by
  have hi : 1 ≤ i.val+1 ∧ i.val+1 ≤ k := ⟨by omega,by omega⟩
  simp only [finiteContactSeeds,dite_eq_left hi,Nat.add_sub_cancel]

end SeededTraceLaw
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_MomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


open MeasureTheory


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteFamilyIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteFamilyIntegral (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : (ℕ → Set E) → ℝ) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η * f (finiteFieldFamily Q J η)

end FiniteFamilyIntegral

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteFieldIntegral (Q : Finset E) (p : ℝ) (f : Set E → ℝ) : ℝ :=
  ∑ ω : FiniteField Q, finiteFieldWeight Q p ω * f (finiteFieldSet Q ω)

end OldPathWeight

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IndependentOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

 
noncomputable def finiteOldKernel (Q : Finset E) (p : ℝ)
    (q : Set E → W → W → ℝ) (a b : W) : ℝ :=
  finiteFieldIntegral Q p (fun ω => q ω a b)

end IndependentOldRun

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointRootMass
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def endpointRootMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (endpoint : I → V) (m : I → ℝ) (ω : Set E) (z : V) : ℝ :=
  ∑ a, if (out a).1 = ω ∧ endpoint a = z then auxiliaryTupleWeight Q J p (out a) * m a else 0

end EndpointRootMass
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldRunArrival
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]

noncomputable def oldRunArrival (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) (A : Finset W) : ℝ :=
  ∑ y : Fin k → W, if oldRunVertices k z y 0 ∈ A then oldRunWeight K k z y else 0

end OldRunArrival

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]


def transportCut (G : BondGraph V E) (n : ℕ) (x y : V) : Prop :=
  y ∈ reachBall G x n ∧ x ∈ reachBall G y n

end NonnegativeTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteTrajectoryMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*} [Fintype W]



noncomputable def finiteTrajectoryMass (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (a : V) : ℝ :=
  finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    ∑ y : Fin k → W, if a ∈ trajectoryUnion G η (e ∘ oldRunVertices k z y) k then
      oldRunWeight (fun i => q (η i)) k z y else 0)

noncomputable def finiteTrajectoryHit (G : BondGraph V E) (e : W → V)
    (Q : Finset E) (p : ℝ) (k : ℕ) (q : Set E → W → W → ℝ) (z : W) (A : Finset V) : ℝ :=
  finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    ∑ y : Fin k → W, if ((A:Set V) ∩ trajectoryUnion G η (e ∘ oldRunVertices k z y) k).Nonempty then
      oldRunWeight (fun i => q (η i)) k z y else 0)

end FiniteTrajectoryMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_EndpointKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceSeparatedMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P₁ P₂ : Type*} [Fintype P₁] [Fintype P₂]

 
noncomputable def finiteChoiceSeparatedPairMass
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (A₁ : P₁ → Finset (SpliceState E)) (A₂ : P₂ → Finset (SpliceState E))
    (y₁ : P₁ → (ℕ → Set E) → ℕ → V) (y₂ : P₂ → (ℕ → Set E) → ℕ → V)
    (m₁ : P₁ → (ℕ → Set E) → ℝ) (m₂ : P₂ → (ℕ → Set E) → ℝ) : ℝ :=
  ∑ a : FiniteChoiceTraceIndex G x k Q A₁ (fun r s => y₁ r s.2),
    ∑ b : FiniteChoiceTraceIndex G x k Q A₂ (fun r s => y₂ r s.2),
    if (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 =
        (choiceTraceOutput G x k Q A₂ (fun r s => y₂ r s.2) b).1 ∧
      choiceTraceCode G x k Q A₁ (fun r s => y₁ r s.2) a ≠ [] ∧
      choiceTraceCode G x k Q A₂ (fun r s => y₂ r s.2) b ≠ [] ∧
      GraphSeparated G
        (cluster G (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x \
          cluster G (choiceTraceInput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x)
        (cluster G (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x \
          cluster G (choiceTraceInput G x k Q A₂ (fun r s => y₂ r s.2) b).1 x)
    then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (pairSpliceOutput (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a)
        (choiceTraceOutput G x k Q A₂ (fun r s => y₂ r s.2) b)) *
      choiceTraceMass G x k Q A₁ (fun r s => y₁ r s.2) (fun s r => m₁ r s.2) a *
      choiceTraceMass G x k Q A₂ (fun r s => y₂ r s.2) (fun s r => m₂ r s.2) b else 0

 
noncomputable def finiteChoiceHit (G : BondGraph V E) (k : ℕ) (Q : Finset E) (p : ℝ)
    (y : P₁ → (ℕ → Set E) → ℕ → V) (m : P₁ → (ℕ → Set E) → ℝ) (B : Set V) : ℝ :=
  ∑ r, finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (B ∩ trajectoryUnion G η (y r η) k).Nonempty then m r η else 0)



end ChoiceSeparatedMass

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMeanKernel
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def finiteBinConnection (G : BondGraph V E) (Q : Finset E) (p : ℝ)
    (x : V) (n : ℕ) (y : V) : ℝ := finiteFieldIntegral Q p (fun ω =>
      if n ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < 2*n ∧ y ∈ cluster G ω x then 1 else 0)

end AmplificationMeanKernel

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MarkedOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}



noncomputable def markedOldRun (K C : ℕ → W → W → ℝ) (k : ℕ) (z : W) (r : Fin k → W) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, oldRunWeight (fun j a b => if j = i then C j a b else K j a b) k z r

end MarkedOldRun

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointSeparated
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterWindowMass (G : BondGraph V E) (Q : Finset E) (p : ℝ)
    (x : V) (lo hi : ℕ) : ℝ :=
  finiteFieldIntegral Q p (fun ω => if (cluster G ω x).Finite ∧
    lo ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < hi then 1 else 0)

end AllEndpointSeparated

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FinitePathExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finitePathTest (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (k : ℕ) (z : ↥B) : ℝ :=
  ∑ r : Fin k → ↥B, oldRunWeight (fun _ a b => K a.val b.val) k z r * F (oldRunVertices k z r 0).val

@[simp] theorem finitePathTest_zero (B : Finset V) (K : V → V → ℝ) (F : V → ℝ) (z : ↥B) :
    finitePathTest B K F 0 z = F z.val := by
  simp [finitePathTest,oldRunWeight,oldRunVertices]

end FinitePathExhaustion

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitDyadicScales
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def weightedWindowProbability {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ) (a b : ℕ) : ℝ :=
  ∑ i, weight i * clusterWindowProbability G p (root i) a b

noncomputable def dyadicBinProbability {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ) (j : ℕ) : ℝ :=
  weightedWindowProbability G p root weight (2^j) (2^(j+1))



end OrbitDyadicScales

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Resampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryCounting
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def firstOpenBridgeCount (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) : ℕ :=
  (Q.filter (fun e => OpenMarkedPivotal G ω {z} x e ∧ bridgeIndex G ω x z e ≤ M)).card

noncomputable def shortClosedBoundaryCount (G : BondGraph V E) (Q : Finset E)
    (x z : V) (M : ℕ) (ω : Finset E) : ℕ :=
  (Q.filter (ShortClosedBoundary G ω x z M)).card

end ShortBoundaryCounting

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClusterResampling
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def resampleClusterAt (G : BondGraph V E) (Q : Finset E)
    (W : Set V) (ω η : Finset E) : Finset E :=
  exteriorBonds G ω W ∪ (η ∩ (Q \ exteriorBonds G Q W))



end ClusterResampling
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ResampledBoundary
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def resampleRootCluster (G : BondGraph V E) (Q : Finset E)
    (z : V) (ω η : Finset E) : Finset E :=
  resampleClusterAt G Q (cluster G ω z) ω η


end ResampledBoundary
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Topology
section RestrictedSelectorBound
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def restrictedSusceptibility (G : BondGraph V E) (S : Set E)
    (p : unitInterval) (x : V) : ℝ :=
  ∑' y, (law p).real {ω | Conn G (ω ∩ S) x y}

end RestrictedSelectorBound
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicBall
attribute [local instance] Classical.propDecidable Classical.decEq

 
def intrinsicBall (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) : Set V :=
  {y | ∃ l : List E, Along G x l y ∧ l.length ≤ M ∧ ∀ e ∈ l, e ∈ ω}

theorem mem_intrinsicBall_self (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) :
    x ∈ intrinsicBall G ω x M := ⟨[],.nil x,Nat.zero_le _,by simp⟩

theorem intrinsicBall_subset_reachBall (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) :
    intrinsicBall G ω x M ⊆ reachBall G x M := by
  rintro y ⟨l,hl,hlen,_⟩
  exact reachBall_mono G x hlen hl.mem_reachBall

end IntrinsicBall
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section IntrinsicMaximum
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBall_exists_max (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) :
    ∃ z ∈ intrinsicBall G ω x M, ∀ y ∈ intrinsicBall G ω x M, f y ≤ f z :=
  Set.exists_max_image _ f ((finite_reachBall hloc x M).subset
    (intrinsicBall_subset_reachBall G ω x M)) ⟨x,mem_intrinsicBall_self G ω x M⟩

noncomputable def intrinsicMaximizer (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (f : V → ℝ) : V :=
  Classical.choose (intrinsicBall_exists_max G hloc ω x M f)

noncomputable def intrinsicPotentialMax (G : BondGraph V E) (ω : Set E)
    (x : V) (M : ℕ) (f : V → ℝ) : ℝ := sSup (f '' intrinsicBall G ω x M)

noncomputable def intrinsicBondSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (M : ℕ) : Finset E :=
  (incidentSupport G hloc (finite_reachBall hloc x M).toFinset).filter (· ∈ S)

end IntrinsicMaximum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section MaximalSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def inducedSusceptibility (G : BondGraph V E) (D : Set V)
    (p : unitInterval) (x : V) : ℝ :=
  if x ∈ D then restrictedSusceptibility G (internalEdges G D) p x else 0

end MaximalSusceptibility
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeletedDomainPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deletedBoundaryPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) : ℝ :=
  ∑ a ∈ ((finite_reachBall hloc x M).toFinset.filter (· ∉ D)),
    ∑ b ∈ neighbors G hloc a, inducedSusceptibility G D p b

noncomputable def deletedLocalPotential (G : BondGraph V E) (D : Set V) (p : unitInterval)
    (ω : Set E) (x : V) (M : ℕ) : ℝ :=
  if x ∈ D then intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) else 0

end DeletedDomainPotential
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_ExteriorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DyadicDiagonalStrata
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def fullOrbitClass (G : BondGraph V E) (o : V) (ω : Set E) (x : V) : Finset V :=
  if h : (cluster G ω x).Finite then h.toFinset.filter (fun y => y ∈ vertexOrbit G o) else ∅

noncomputable def diagonalLossMass (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (ω : Set E) (x : V) : ℝ :=
  ((cluster G ω x).ncard:ℝ)^2 * ∑ z ∈ fullOrbitClass G o ω x, K x z

end DyadicDiagonalStrata
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DiagonalSeries
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def diagonalLossTerm (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x y : V) (ω : Set E) : ℝ :=
  if y ∈ vertexOrbit G o ∧ Conn G ω x y then K x y*((cluster G ω x).ncard:ℝ)^2 else 0

end DiagonalSeries
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshExteriorMoment
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def freshExteriorMoment (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ :=
  ((cluster G ω x).ncard:ℝ) * inducedSusceptibility G (cluster G ω x)ᶜ p y

end FreshExteriorMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def distinctClusterMoment (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) ∂law p

noncomputable def neighborClusterMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) : ℝ :=
  ∑ y ∈ neighbors G hloc x, distinctClusterMoment G p x y

noncomputable def rootNeighborMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (p : unitInterval) : ℝ :=
  ∑ i, weight i * neighborClusterMoment G hloc p (root i)

end DistinctClusterMoments
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedBoundaryPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exposedVertexPotential (G : BondGraph V E) (p : unitInterval)
    (x a b : V) (ω : Set E) : ℝ :=
  if Conn G ω x a then freshExteriorMoment G p a b ω else 0

end ExposedBoundaryPotential
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePotentialIteration
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realAction (A : Hilbert V →L[ℂ] Hilbert V) (f : V → ℝ) (x : V) : ℝ :=
  ∑' y, (matrixCoeff A x y).re*f y

end PositivePotentialIteration
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PivotalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def pivotalTransportMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x a : V) : ℝ :=
  ∑ b ∈ neighbors G hloc a, ∑' y, (law p).real (orientedPivotalEvent G x y a b)

end PivotalTransport
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section FiniteRootPivotalApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteRootPivotalMass (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (Q : Finset E) (F : Finset V) : ℝ :=
  ∑ i, weight i*(∑ y ∈ F, ∑ e ∈ Q, (law p).real (closedPivotal {ω | Conn G ω (root i) y} e))

end FiniteRootPivotalApproximation
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_FractionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {E : Type v}
section DecisionCovarianceAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteCovariance (Q : Finset E) (p : ℝ) (f g : Finset E → ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => f ω*g ω) p - bernoulliPolynomial Q f p*bernoulliPolynomial Q g p

end DecisionCovarianceAlgebra
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededEdgeSearch
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def seededEdgeSearch (G : BondGraph V E) (x : V) :
    ℕ → Finset E → Finset V → EdgeQueryTree E
  | 0, _, R => .done (decide (x ∈ R))
  | n+1, Q, R =>
    if hc : SearchCrossing G Q R then
      let t := searchCrossing G Q R hc
      .query t.1 (seededEdgeSearch G x n (Q.erase t.1) R)
        (seededEdgeSearch G x n (Q.erase t.1) (insert t.2.2 R))
    else .done (decide (x ∈ R))

end SeededEdgeSearch
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RandomizedDecisionCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteSeedProbability (G : BondGraph V E) (F : Finset V)
    (ω : Finset E) (x : V) (h : ℝ) : ℝ :=
  bernoulliPolynomial F (fun m => if ∃ y ∈ m, Conn G (ω:Set E) x y then 1 else 0) h

end RandomizedDecisionCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterTailCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterTailIndicator (G : BondGraph V E) (x : V) (n : ℕ)
    (ω : Finset E) : ℝ := if n ≤ (finiteRootComponent G ω x).card then 1 else 0

noncomputable def finiteClusterTail (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : ℝ) : ℝ :=
  bernoulliPolynomial Q (finiteClusterTailIndicator G x n) p

end ClusterTailCovariance
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceExploration
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def incidencePick (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : IncidencePending G Q R) : E × V × V := Classical.choose h

noncomputable def incidenceSearch (G : BondGraph V E) :
    ℕ → Finset E → Finset V → EdgeQueryTree E
  | 0, _, _ => .done false
  | n+1, Q, R =>
    if hc : IncidencePending G Q R then
      let t := incidencePick G Q R hc
      .query t.1 (incidenceSearch G n (Q.erase t.1) R)
        (incidenceSearch G n (Q.erase t.1) (insert t.2.2 R))
    else .done false

end IncidenceExploration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorExplorationLaw
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def exteriorSearchScore (G : BondGraph V E) (n : ℕ) (Q : Finset E)
    (x v : V) (p : ℝ) (ω : Finset E) : ℝ :=
  let W := finiteRootComponent G ω x
  if v ∈ W then 0 else
    (incidenceSearch G n (exteriorBonds G Q (W:Set V)) {v}).score p (exteriorBonds G ω (W:Set V))

end ExteriorExplorationLaw
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_LargeContacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def fullContactBin (G : BondGraph V E) (x v : V) (n m : ℕ) (ω : Set E) : ℝ :=
  if ¬Conn G ω x v ∧ n ≤ min (cluster G ω x).ncard (cluster G ω v).ncard ∧
    min (cluster G ω x).ncard (cluster G ω v).ncard ≤ m
  then clusterContactCount G ω x v else 0

end InfiniteContacts
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ContactTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section IndexedEdgeKernel
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def indexedEdgeKernel (G : BondGraph V E) (x y : V) : ℝ≥0∞ :=
  ∑' e, if G e = s(x,y) then 1 else 0

end IndexedEdgeKernel
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section NonnegativeOperatorDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def ennMatrixCoeff (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) : ℝ≥0∞ :=
  ENNReal.ofReal (matrixCoeff A x y).re

end NonnegativeOperatorDiagram
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteClusterKernel
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClusterWeight (G : BondGraph V E) (f : V → ℝ)
    (x : V) (ω : Finset E) : ℝ := ∑ y ∈ finiteRootComponent G ω x, f y

noncomputable def finitePairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (ω : Finset E) (x y : V) : ℝ :=
  ∑ a ∈ finiteRootComponent G ω x, finiteClusterWeight G (J a) y ω

end FiniteClusterKernel
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallFinitePairKernel
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteSmallPairKernel (G : BondGraph V E) (J : V → V → ℝ)
    (L : ℝ) (x y : V) (ω : Finset E) : ℝ :=
  if (finiteRootComponent G ω x).card < L ∧ ¬Conn G (ω:Set E) x y then finitePairKernel G J ω x y else 0

noncomputable def finiteSmallClusterSize (G : BondGraph V E) (L : ℝ) (x : V) (ω : Finset E) : ℝ :=
  if (finiteRootComponent G ω x).card < L then (finiteRootComponent G ω x).card else 0


end SmallFinitePairKernel
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section SmallKernelLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def smallPairKernel (G : BondGraph V E) (J : V → V → ℝ≥0∞)
    (L : ℝ) (x y : V) (ω : Set E) : ℝ≥0∞ :=
  if ((cluster G ω x).ncard:ℝ) < L ∧ ¬Conn G ω x y then clusterPairKernel G ω J x y else 0

end SmallKernelLimit
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_RussoRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section LargeContactCauchySchwarz
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def largeContactKernel (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) then
    clusterPairKernel G ω (indexedEdgeKernel G) x y else 0

end LargeContactCauchySchwarz
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionRussoContacts
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteClosedContact (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) : ℝ :=
  if ¬Conn G (ω:Set E) x y then
    (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω y)).card else 0

end ConnectionRussoContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def russoDiagram (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, indexedEdgeKernel G a b *
    (law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b})

end RussoDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoMajorant
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def russoSlope (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  realContactExpectation G x y t / (1-t)

noncomputable def russoMajorant (G : BondGraph V E) (b : unitInterval) (x y : V) : ℝ :=
  (russoDiagram G b x y).toReal / (1-(b:ℝ))

end RussoMajorant
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RealTriangle
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realTriangleTerm (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) : ℝ :=
  realTwoPoint G x ab.1 t * realTwoPoint G ab.1 ab.2 t * realTwoPoint G ab.2 x t

noncomputable def realTriangleSlope (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) : ℝ :=
  russoSlope G x ab.1 t * realTwoPoint G ab.1 ab.2 t * realTwoPoint G ab.2 x t +
  realTwoPoint G x ab.1 t * russoSlope G ab.1 ab.2 t * realTwoPoint G ab.2 x t +
  realTwoPoint G x ab.1 t * realTwoPoint G ab.1 ab.2 t * russoSlope G ab.2 x t

noncomputable def triangleMajorant (G : BondGraph V E) (b : unitInterval) (x : V) (ab : V×V) : ℝ :=
  russoMajorant G b x ab.1 * twoPoint G b ab.1 ab.2 +
  twoPoint G b x ab.1 * russoMajorant G b ab.1 ab.2 +
  russoMajorant G b x ab.2 * twoPoint G b ab.2 ab.1

end RealTriangle
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TriangleDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realTriangle (G : BondGraph V E) (x : V) (t : ℝ) : ℝ :=
  ∑' ab, realTriangleTerm G x ab t

noncomputable def rootTriangle (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * realTriangle G (root i) t

end TriangleDerivative
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TraceSquareRoot
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rootTriangleSqrt (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ := Real.sqrt (rootTriangle G root weight t)

end TraceSquareRoot
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NormRatio
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def maxSusceptibility (G : BondGraph V E) (p : unitInterval) : ℝ :=
  sSup (Set.range (susceptibility G p))

end NormRatio
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_ClusterProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster Products for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedClusterMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) : ℝ :=
  ∑' y, deformedConnection G P p k t D ω x y

end ExteriorWeightedConnections
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshWeightedMass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedFreshExteriorMoment (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) (ω : Set E) : ℝ :=
  deformedClusterMass G P p k t D ω x *
    deformedSusceptibility G P p k t (D \ cluster G (ω ∩ internalEdges G D) x) y

end FreshWeightedMass
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SizeWeightedPotential
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def sizeMembership (G : BondGraph V E) (x a : V) (ω : Set E) : ℝ :=
  if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0

noncomputable def sizeWeightedConnectionPotential (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ := ∑' a, sizeMembership G x a ω * twoPoint G p y a

end SizeWeightedPotential
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LiteralDeformationDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedDerivativeMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) : ℝ :=
  ∑' y, corridorPenalty G P p k D ω x y * deformedConnection G P p k t D ω x y

end LiteralDeformationDerivative
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorLegObservable
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def exteriorLegProduct (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) : ℝ :=
  if ¬Conn G (w.exterior ω) w.base w.endpoint then
    deformedConnection G P p k t (w.interior : Set V)ᶜ ω x w.base *
      deformedConnection G P p k t (w.interior : Set V)ᶜ ω w.endpoint y else 0

end ExteriorLegObservable
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_AveragedDecrease
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformationCovariance
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def corridorDerivativeContribution (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (x y : V) : ℝ :=
  ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
    deformedConnection G P p k t Set.univ ω x y ∂law p

end DeformationCovariance
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DerivativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def derivativeTransportMass (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (x u : V) : ℝ :=
  ∑' w : RawFrom (openSimpleGraph G Set.univ) k u,
    ∑' y, corridorDerivativeContribution G P p t ⟨u,w⟩ x y

end DerivativeTransport
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PathAverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

noncomputable def rawPathAverage (G : BondGraph V E) (P : V → V → ℝ) (k : ℕ)
    (root : ι → V) (weight : ι → ℝ) (f : RawCorridor G k → ℝ) : ℝ :=
  ∑ i, weight i * ∑' w : RawFrom (openSimpleGraph G Set.univ) k (root i),
    w.2.mass P * f ⟨root i,w⟩

noncomputable def retainedSusceptibilityProduct (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) {k : ℕ} (t : ℝ) (w : RawCorridor G k) : ℝ :=
  if 3 ≤ w.path.length then
    deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.base *
      deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.endpoint
  else 0

end PathAverage
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]


theorem mem_segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) (s : I → V) :
    s ∈ segmentAnchors G hloc γ n hdiam i x ↔ s ∈ segmentOrbit G γ ∧ s i = x := by
  exact Set.Finite.mem_toFinset _

end AnchoredSegments
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

noncomputable def labelFromCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (c : RootedLabelCode G hloc γ n hdiam center ep neg L m x) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} := by
  rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
  have hsm := ((mem_segmentAnchors G hloc γ n hdiam center x s).mp hs).1
  have hsx := ((mem_segmentAnchors G hloc γ n hdiam center x s).mp hs).2
  have hhm := ((mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh).1
  have hhz := ((mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh).2
  subst z
  exact ⟨⟨s,hsm,h,hhm,mid,α,β⟩,hsx⟩

noncomputable def labelToCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V)
    (ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x}) :
    RootedLabelCode G hloc γ n hdiam center ep neg L m x :=
  ⟨⟨ξ.1.first,(mem_segmentAnchors G hloc γ n hdiam center x ξ.1.first).mpr ⟨ξ.1.first_mem,ξ.2⟩⟩,
    ⟨ξ.1.last ep,ξ.1.middle⟩,
    ⟨ξ.1.last,(mem_segmentAnchors G hloc γ n hdiam ep (ξ.1.last ep) ξ.1.last).mpr ⟨ξ.1.last_mem,rfl⟩⟩,
    ξ.1.leftTail,ξ.1.rightTail⟩

noncomputable def rootedLabelEquiv (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} ≃
      RootedLabelCode G hloc γ n hdiam center ep neg L m x where
  toFun := labelToCode G hloc γ n hdiam center ep neg L m x
  invFun := labelFromCode G hloc γ n hdiam center ep neg L m x
  left_inv ξ := by
    cases ξ with
    | mk ξ hξ => cases ξ; rfl
  right_inv c := by
    rcases c with ⟨⟨s,hs⟩,⟨z,mid⟩,⟨h,hh⟩,α,β⟩
    have hh' := (mem_segmentAnchors G hloc γ n hdiam ep z h).mp hh
    obtain ⟨hhm,hhz⟩ := hh'
    subst z
    rfl

end FiniteRootedLabels
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

noncomputable def segmentReturnMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (ep : I) (L : ℕ) (x : V) : ℝ :=
  ∑' mid : RawFrom (openSimpleGraph G Set.univ) L x,
    if mid.1 ∈ vertexOrbit G (γ ep) then mid.2.mass (walkKernel G hloc a) else 0

end LabeledMass
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledNormalization
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]



noncomputable def escapeLabelProbability (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (ξ : EscapeLabel G γ ep neg L m) : ℝ :=
  ξ.mass (walkKernel G hloc a) /
    (((segmentAnchors G hloc γ n hdiam center (γ center)).card : ℝ) *
      ((segmentAnchors G hloc γ n hdiam ep (γ ep)).card : ℝ) *
      segmentReturnMass G hloc a γ ep L (γ ep))

end LabeledNormalization
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def labelEndpointEquiv (center : I) (x : V) :
    (Σ y : V, {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}) ≃
      {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x} where
  toFun ξ := ⟨ξ.2.1,ξ.2.2.1⟩
  invFun ξ := ⟨ξ.1.last center,ξ.1,ξ.2,rfl⟩
  left_inv ξ := by rcases ξ with ⟨y,ξ,hx,hy⟩; subst y; rfl
  right_inv ξ := rfl

def labelAutPairEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (center : I) (x y : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = a x ∧ ξ.last center = a y} where
  toFun ξ := ⟨EscapeLabel.autMap hab ξ.1,congrArg a ξ.2.1,congrArg a ξ.2.2⟩
  invFun ξ := ⟨EscapeLabel.autMap (isAut_symm G hab) ξ.1,by
    change a.symm (ξ.1.first center) = x ∧ a.symm (ξ.1.last center) = y
    rw [ξ.2.1,ξ.2.2,a.symm_apply_apply,a.symm_apply_apply]
    exact ⟨rfl,rfl⟩⟩
  left_inv ξ := Subtype.ext (EscapeLabel.autMap_symm hab ξ.1)
  right_inv ξ := Subtype.ext (EscapeLabel.autMap_symm (isAut_symm G hab) ξ.1)

noncomputable def escapeLabelTransport (center : I) (B : EscapeLabel G γ ep neg L m → ℝ) (x y : V) : ℝ :=
  ∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y}, B ξ.1

end LabeledTransport
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GeodesicSegments
attribute [local instance] Classical.propDecidable Classical.decEq

 

def geodesicSegment (G : BondGraph V E) {x y : V}
    (q : (openSimpleGraph G Set.univ).Walk x y) (N : ℕ) : Fin (N+1) → V :=
  fun i => q.getVert i

theorem segmentOrbit_adj (G : BondGraph V E) {I : Type*} (γ s : I → V)
    (hs : s ∈ segmentOrbit G γ) (i j : I) (hij : (openSimpleGraph G Set.univ).Adj (γ i) (γ j)) :
    (openSimpleGraph G Set.univ).Adj (s i) (s j) := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  exact (autSimpleGraph G hab).map_rel_iff.mpr hij

end GeodesicSegments
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_CollisionTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IntrinsicVisibleBlocks
attribute [local instance] Classical.propDecidable Classical.decEq

def positiveStem (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) :
    HoldingWalk H J (s (segmentCenter J)) (s (Fin.last (J+J))) :=
  HoldingWalk.fromPositions J (segmentPositivePositions J s) (fun i => hs ⟨J+i.val,by omega⟩)

theorem orbitSegment_consecutive (G : BondGraph V E) (J : ℕ) (γ s : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hs : s ∈ segmentOrbit G γ) :
    ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (s i.castSucc) (s i.succ) :=
  fun i => segmentOrbit_adj G γ s hs _ _ (hγ i)

 

def escapeLabelRaw (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    HoldingWalk (openSimpleGraph G Set.univ) ((J+L)+J)
      (ξ.first (segmentCenter J)) (ξ.last (segmentCenter J)) :=
  (positiveStem _ J ξ.first (orbitSegment_consecutive G J γ ξ.first hγ ξ.first_mem)).append
    (ξ.middle.append (positiveStem _ J ξ.last
      (orbitSegment_consecutive G J γ ξ.last hγ ξ.last_mem)).reverse)

end IntrinsicVisibleBlocks
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RootedRawProjection
attribute [local instance] Classical.propDecidable Classical.decEq

def rootedEscapeLabelRaw (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (x : V) (ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x}) :
    RawFrom (openSimpleGraph G Set.univ) ((J+L)+J) x := by
  rcases ξ with ⟨ξ,hξ⟩
  subst x
  exact ⟨ξ.last (segmentCenter J),escapeLabelRaw G J L m γ hγ ξ⟩

end RootedRawProjection
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PositiveEscapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Escapes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CombinedRawAvoidance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

 

def firstEscapeCollision (G : BondGraph V E) (J m L : ℕ) (x y : V)
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (tail : RawFrom (openSimpleGraph G Set.univ) m x)
    (mid : RawFrom (openSimpleGraph G Set.univ) L y) (h : I → V) : Prop :=
  (((∃ s, pos s ∈ tail.2.vertices) ∨ (∃ s, neg s ∈ mid.2.vertices)) ∨
    (∃ z, z ∈ tail.2.vertices ∧ z ∈ mid.2.vertices)) ∨
  ((∃ st : Fin (J+1) × Fin (J+1), h (j st.1) = neg st.2) ∨
    (∃ ij : Fin (m+1) × Fin (J+1), tail.2.position ij.1.val = h (j ij.2)))

end CombinedRawAvoidance
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FirstLabeledMarginal
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
def labelFirstEscapeCollision (G : BondGraph V E) (γ : I → V) (ep neg : I)
    (J L m : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (ξ : EscapeLabel G γ ep neg L m) : Prop :=
  firstEscapeCollision G J m L (ξ.first neg) (ξ.first ep)
    (fun t => ξ.first (posIdx t)) (fun t => ξ.first (negIdx t)) suffixIdx
    ξ.leftTail ⟨ξ.last ep,ξ.middle⟩ ξ.last

end FirstLabeledMarginal
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_SelectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FullPotentialTests
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

 
def labelPotentialFailure (G : BondGraph V E) (p : unitInterval) (γ : I → V)
    (ep neg : I) (L m : ℕ)
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (t : ℝ) (ξ : EscapeLabel G γ ep neg L m) : Prop :=
  (t < ∑ b ∈ F ξ.first ⟨ξ.last ep,ξ.middle⟩ ξ.last, twoPoint G p ξ.leftTail.1 b) ∨
  (t < ∑ b ∈ F ξ.first ⟨ξ.last ep,ξ.middle⟩ ξ.last, twoPoint G p ξ.rightTail.1 b)

end FullPotentialTests
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PathSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


def negativeStem (H : SimpleGraph V) (J : ℕ) (s : Fin (J+J+1) → V)
    (hs : ∀ i : Fin (J+J), H.Adj (s i.castSucc) (s i.succ)) :
    HoldingWalk H J (s (segmentCenter J)) (s 0) :=
  (HoldingWalk.fromPositions J (fun i => s ⟨i.val,by omega⟩)
    (fun i => hs ⟨i.val,by omega⟩)).reverse


def labelLeftEscape (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) :
    HoldingWalk (openSimpleGraph G Set.univ) (m+J)
      (ξ.first (segmentCenter J)) ξ.leftTail.1 :=
  (negativeStem _ J ξ.first (orbitSegment_consecutive G J γ ξ.first hγ ξ.first_mem)).append ξ.leftTail.2

 
def labelCorridor (G : BondGraph V E) (J L m : ℕ) (γ : Fin (J+J+1) → V)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m) : RawCorridor G ((J+L)+J) :=
  ⟨ξ.first (segmentCenter J), ξ.last (segmentCenter J), escapeLabelRaw G J L m γ hγ ξ⟩



noncomputable def spineVertices (G : BondGraph V E) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) : Finset V :=
  Finset.univ.image (s ∘ segmentPositiveIndex J) ∪ mid.2.vertices.toFinset ∪
    Finset.univ.image (h ∘ segmentPositiveIndex J)

noncomputable def spineNeighborhood (G : BondGraph V E) (hloc : LocallyFinite G) (J L : ℕ)
    (s : Fin (J+J+1) → V)
    (mid : RawFrom (openSimpleGraph G Set.univ) L (s (Fin.last (J+J))))
    (h : Fin (J+J+1) → V) : Finset V :=
  let W := spineVertices G J L s mid h
  W ∪ W.biUnion (neighbors G hloc)

end EscapeGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Cayley_Folner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The group Følner criterion and nonamenable Cayley graphs. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u
section GroupGeometry
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] lemma rightTranslate_one (A : Finset Λ) : rightTranslate A 1 = A := by
  simp [rightTranslate]

noncomputable def rightDefect (A : Finset Λ) (g : Λ) : ℕ :=
  (rightTranslate A g \ A).card

end GroupGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_IntrinsicDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic distance and closest vertices in percolation clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def openAutIso (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (h : IsAut G a b) (ω : Set E) :
    openSimpleGraph G (b ⁻¹' ω) ≃g openSimpleGraph G ω where
  toEquiv := a
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hxy,e,he,heq⟩
      refine ⟨fun hh => hxy (congrArg a hh),b.symm e,by simpa using he,?_⟩
      have hh := (isAut_symm G h) e
      rw [heq,Sym2.map_mk] at hh
      simpa only [Equiv.symm_apply_apply] using hh
    · rintro ⟨hxy,e,he,heq⟩
      exact ⟨fun hh => hxy (a.injective hh),b e,he,by rw [h,heq,Sym2.map_mk]⟩

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_NearestMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nearest-vertex transport and its finite incoming mass. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def nearestMass (G : BondGraph V E) (A : Set E → Set V)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y ∈ closest (openSimpleGraph G ω) (A ω) x then
    ((closest (openSimpleGraph G ω) (A ω) x).ncard : ℝ≥0∞)⁻¹ else 0

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encounter vertices and infinite open branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

def encounters (G : BondGraph V E) (ω : Set E) : Set V := {x | IsEncounter G ω x}

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Counts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting encounter vertices by mass transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def cutIso {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (x : V) : cutVertex H x ≃g cutVertex K (f x) where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro a b
    change (K.Adj (f a) (f b) ∧ f a ≠ f x ∧ f b ≠ f x) ↔
      (H.Adj a b ∧ a ≠ x ∧ b ≠ x)
    simp only [f.map_adj_iff,f.injective.ne_iff]

noncomputable def markedCluster (G : BondGraph V E) (ω η : Set E) (x : V) : Finset V :=
  (clusterFinset G η x).filter (IsEncounter G ω)

noncomputable def encounterCount (G : BondGraph V E) (ω η : Set E) (x : V) : ℕ :=
  if IsEncounter G ω x then branchCount (openSimpleGraph G ω) (markedCluster G ω η x) x else 0

end Percolation

end OAI
end


