-- Prove2me | Definitions.Def_OAIQ229C033
-- name    : OAIQ229C033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:00:05.589003+00:00
-- url     : https://prove2.me/theorems/b61782e2-3584-4327-a224-c3c74b780761
-- title:
--   Definitions bundle OAIQ229C033 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 21 definitions and 12 theorems. The definitions and types are `OAI.CoarseAssembly.explicitBoundaryClass`, `OAI.CoarseAssembly.explicitBoundaryStage`, `OAI.CoarseAssembly.explicitCircleFamily`, `OAI.CoarseAssembly.explicitCounterexampleClass`, `OAI.CoarseAssembly.explicitFiberClass`, `OAI.CoarseAssembly.explicitFiberStage`, `OAI.CoarseAssembly.explicitRealFiberStage`, `OAI.NuclearUltrapower.SOS.generator10`, `OAI.NuclearUltrapower.SOS.generator11`, `OAI.NuclearUltrapower.SOS.generator2`, `OAI.NuclearUltrapower.SOS.generator3`, `OAI.NuclearUltrapower.SOS.generator4`, `OAI.NuclearUltrapower.SOS.generator5`, `OAI.NuclearUltrapower.SOS.generator6`, `OAI.NuclearUltrapower.SOS.generator7`, `OAI.NuclearUltrapower.SOS.generator8`, `OAI.NuclearUltrapower.SOS.generator9`, `OAI.NuclearUltrapower.SOS.gramPolyRow`, `OAI.NuclearUltrapower.SOS.gramValue`, `OAI.NuclearUltrapower.SOS.matrixWord`, `OAI.NuclearUltrapower.SOS.rootPairs`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BoundedFamilyHomotopy`, `CoarseAssembly_BoundedFamilySubdivision`, `CoarseAssembly_ControlledBoundaryNearby`, `CoarseAssembly_DirectSumIntertwining`, `CoarseAssembly_ExplicitBoundaryConclusion`, `CoarseAssembly_ExplicitCircleFamily`, `CoarseAssembly_ExplicitPersistence`, `CoarseAssembly_RipsEmbeddingIndependence`, `CoarseAssembly_RipsFiniteTail`, `CoarseAssembly_RipsUnitaryFamily`, `CoarseAssembly_SampledRipsEstimates`, `NuclearUltrapower_IntegerMatrices`, `NuclearUltrapower_IntegralCertificate`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C028`, `OAIQ229C029` and `OAIQ229C031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C035` and `OAIQ229C036`; the statement `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_certificate`; the proofs of `OAI_CoarseAssembly_elementaryKernel_projection`, `OAI_CoarseAssembly_provedKazhdanInput`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_certificate` and `OAI_NuclearUltrapower_SOS_basis_good`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C028
import Definitions.Def_OAIQ229C029
import Definitions.Def_OAIQ229C031

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsEmbeddingIndependence
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-union Rips boundaries are independent of the ample embeddings -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ripsFamilyBoundaryWithEmbeddings_independent (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C)
    (V W : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc V =
      ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc W := by
  let := separatedMetric o
  apply coefficientFamilyBoundary_independent

/-- The previously constructed ample boundary is the representative with the chosen embeddings. -/
theorem ampleRipsFamilyBoundary_eq_withEmbeddings (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hc =
      ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc
        (fun i => ampleIsometry (c i).space) := by
  let := separatedMetric o
  apply separatedFamilyBoundary_bound_independent
  · exact fun i => ampleRipsOperator_selfAdjoint r (c i) (hπ i) (hF i)
  · exact fun i => ampleRipsOperator_square_compact r (c i) (hπ i) (hF i)

/-- In particular, every choice of ample embeddings gives the existing whole-union class. -/
theorem ampleRipsFamilyBoundary_embeddings (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖(c i).operator‖ ≤ C)
    (V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hc =
      ripsFamilyBoundaryWithEmbeddings o r hr c hπ hF C hC hc V := by
  let := separatedMetric o
  exact (ampleRipsFamilyBoundary_eq_withEmbeddings o r hr c hπ hF C hC hc).trans
    (ripsFamilyBoundaryWithEmbeddings_independent o r hr c hπ hF C hC hc _ V)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DirectSumIntertwining
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum inclusions intertwine the actual localized operators -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d e : OddCycle C(Point X r, ℂ)}

theorem ripsSpatialOperator_directSum_right (h : c.IsDirectSum d e)
    (hd : d.representation 1 = 1) (he : e.representation 1 = 1) :
    (ripsSpatialOperator r e he).comp (coefficientIsometry h.right).toContinuousLinearMap =
      (coefficientIsometry h.right).toContinuousLinearMap.comp (ripsSpatialOperator r d hd) := by
  apply localizedSpatialOperator_intertwines h.right
    (representedSqrt r d) (representedSqrt r e)
    (representedSqrt_adjoint r d) (representedSqrt_adjoint r e)
    (representedSqrt_partition r d hd) (representedSqrt_partition r e he)
  · intro x v
    change e.representation (sqrtCoordinate r x) (h.right v) = _
    rw [h.representation_eq]
    exact h.block_apply_right _ _ v
  · intro v
    rw [h.operator_eq]
    exact h.block_apply_right _ _ v

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsUnitaryFamily
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-union boundary invariance under unitary equivalence of cycles -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d : OddCycle C(Point X r, ℂ)}

theorem ripsExtension_aligned (e : c.UnitaryEquivalent d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1)
    (V : c.space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    coefficientExtension (V.comp e.unitary.symm.toLinearIsometry) (ripsSpatialOperator r d hd) =
      coefficientExtension V (ripsSpatialOperator r c hc) := by
  rw [ripsSpatialOperator_unitary r e hc hd]
  change isometricExtension (coefficientIsometry (V.comp e.unitary.symm.toLinearIsometry))
    (isometricExtension (coefficientIsometry e.unitary.toLinearIsometry) _) = _
  rw [isometricExtension_comp, coefficientIsometry_comp]
  have he : (V.comp e.unitary.symm.toLinearIsometry).comp e.unitary.toLinearIsometry = V := by
    ext x
    simp
  rw [he]
  rfl

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ripsFamilyBoundaryWithEmbeddings_congr (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d : ∀ i, OddCycle C(Point (Q i) r, ℂ))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator) (hG : ∀ i, IsSelfAdjoint (d i).operator)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hnc : ∀ i, ‖(c i).operator‖ ≤ C) (hnd : ∀ i, ‖(d i).operator‖ ≤ D)
    (V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (W : ∀ i, (d i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hVW : ∀ i, coefficientExtension (V i) (ripsSpatialOperator r (c i) (hc i)) =
      coefficientExtension (W i) (ripsSpatialOperator r (d i) (hd i))) :
    letI := separatedMetric o
    ripsFamilyBoundaryWithEmbeddings o r hr c hc hF C hC hnc V =
      ripsFamilyBoundaryWithEmbeddings o r hr d hd hG D hD hnd W := by
  let := separatedMetric o
  unfold ripsFamilyBoundaryWithEmbeddings coefficientFamilyBoundary
  apply separatedFamilyBoundary_congr
  exact funext hVW

theorem ampleRipsFamilyBoundary_unitary (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (e : ∀ i, (c i).UnitaryEquivalent (d i))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator) (hG : ∀ i, IsSelfAdjoint (d i).operator)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hnc : ∀ i, ‖(c i).operator‖ ≤ C) (hnd : ∀ i, ‖(d i).operator‖ ≤ D) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hc hF C hC hnc =
      ampleRipsFamilyBoundary o r hr d hd hG D hD hnd := by
  let := separatedMetric o
  let V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
    fun i => ampleIsometry (c i).space
  let W : ∀ i, (d i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
    fun i => (V i).comp (e i).unitary.symm.toLinearIsometry
  calc
    _ = ripsFamilyBoundaryWithEmbeddings o r hr c hc hF C hC hnc V :=
      ampleRipsFamilyBoundary_embeddings o r hr c hc hF C hC hnc V
    _ = ripsFamilyBoundaryWithEmbeddings o r hr d hd hG D hD hnd W :=
      ripsFamilyBoundaryWithEmbeddings_congr o r hr c d hc hd hF hG C D hC hD hnc hnd V W
        (fun i => (ripsExtension_aligned r (e i) (hc i) (hd i) (V i)).symm)
    _ = _ := (ampleRipsFamilyBoundary_embeddings o r hr d hd hG D hD hnd W).symm

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledRipsEstimates
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the localized finite sums used in homotopy telescoping -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem sampledFiniteSum_ample_sub_norm_le
    (r : ℝ) (h : OddHomotopy C(Point X r, ℂ)) (χ : C(Point X r, ℂ) →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (hπ : ∀ t, h.representation t 1 = 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hop : ∀ j, j < N → ‖h.operator (τ j) - h.operator (σ j)‖ ≤ δ)
    (hrep : ∀ x j, j < N → ‖h.representation (τ j) (sqrtCoordinate r x) -
      h.representation (σ j) (sqrtCoordinate r x)‖ ≤ δ) :
    ‖ampleRipsOperator r (sampledFiniteSum h χ N τ C hC hF)
        (sampledFiniteSum_unital h χ N τ C hC hF hπ) -
      ampleRipsOperator r (sampledFiniteSum h χ N σ C hC hF)
        (sampledFiniteSum_unital h χ N σ C hC hF hπ)‖ ≤
      δ + (4 * C + 2) * ((Fintype.card X : ℝ) * δ) := by
  apply (coefficientExtension_sub_norm_le (ampleIsometry (repeatedHilbert h.space)) _ _).trans
  apply (localizedSpatialOperator_variation_norm_le _ _ _ _ _ _ C
    (sampledFiniteSum_norm_le h χ N σ C hC hF)).trans
  exact add_le_add (sampledFiniteSum_operator_sub_norm_le h χ N τ σ C hC hF δ hδ hop)
    (mul_le_mul_of_nonneg_left
      (sampledFiniteSum_partition_sub_norm_le r h χ N τ σ C hC hF δ hδ hrep)
      (by linarith))

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedFamilyHomotopy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded analytic homotopies without uniform continuity assumptions -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] (r : ℝ)

variable {Q r}

namespace BoundedFamilyHomotopy

theorem sample_rotate_boundary (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval) :
    (h.sample χ (fun i => N i + 1) (fun i => lastEndpointFirst (N i) (τ i))).boundary o hr =
      (h.sample χ (fun i => N i + 1) (fun i j => τ i (j + 1))).boundary o hr := by
  let := separatedMetric o
  exact ampleRipsFamilyBoundary_unitary o r hr _ _
    (fun i => sampledFiniteSum_rotate (h.homotopy i) (χ i) (N i) (τ i)
      h.bound h.one_le_bound (fun t => h.norm_le t i)) _ _ _ _ _ _ _ _ _ _

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ControlledBoundaryNearby
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm comparison of bounded cycle families in the actual Roe boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem ControlledCycleFamily.boundary_eq_of_ample_nearby
    (c d : ControlledCycleFamily Q r) (o : ∀ i, Q i) (hr : 0 ≤ r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ < 1 / 4)
    (hnear : ∀ i, ‖ampleRipsOperator r (d.cycle i) (d.unital i) -
      ampleRipsOperator r (c.cycle i) (c.unital i)‖ ≤ δ) :
    c.boundary o hr = d.boundary o hr := by
  let := separatedMetric o
  exact separatedFamilyBoundary_eq_of_nearby o _ _ (c.bound + 4) (d.bound + 4)
    (by linarith [c.bound_nonneg]) (by linarith [d.bound_nonneg])
    (fun i => (ampleRipsOperator_norm_le r (c.cycle i) (c.unital i)).trans
      (add_le_add (c.norm_le i) le_rfl))
    (fun i => (ampleRipsOperator_norm_le r (d.cycle i) (d.unital i)).trans
      (add_le_add (d.norm_le i) le_rfl))
    (r + r) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator_propagation r hr (d.cycle i) (d.unital i))
    (fun i => ampleRipsOperator_selfAdjoint r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_selfAdjoint r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    δ hδ hsmall hnear

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedFamilySubdivision
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component-dependent subdivisions with uniformly close sampled Roe operators -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

namespace BoundedFamilyHomotopy

theorem sampled_boundary_eq (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval)
    (hstep : ∀ i j, j < N i + 1 →
      ‖(h.homotopy i).operator (τ i (j + 1)) - (h.homotopy i).operator (τ i j)‖ ≤
        h.samplingTolerance i ∧
      ∀ x, ‖(h.homotopy i).representation (τ i (j + 1)) (sqrtCoordinate r x) -
        (h.homotopy i).representation (τ i j) (sqrtCoordinate r x)‖ ≤ h.samplingTolerance i) :
    (h.sample χ (fun i => N i + 1) τ).boundary o hr =
      (h.sample χ (fun i => N i + 1) (fun i j => τ i (j + 1))).boundary o hr := by
  apply ControlledCycleFamily.boundary_eq_of_ample_nearby _ _ o hr (1 / 8)
    (by norm_num) (by norm_num)
  intro i
  exact (sampledFiniteSum_ample_sub_norm_le r (h.homotopy i) (χ i) (N i + 1)
    (fun j => τ i (j + 1)) (τ i) h.bound h.one_le_bound (fun t => h.norm_le t i)
    (fun t => h.unital t i) (h.samplingTolerance i) (h.samplingTolerance_pos i).le
    (fun j hj => (hstep i j hj).1) (fun x j hj => (hstep i j hj).2 x)).trans
    (h.samplingTolerance_estimate i).le

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitCircleFamily
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The circle-family class without a countable-additivity assumption -/

noncomputable section

namespace CoarseAssembly

open Analytic
open scoped ZeroAtInfty

/-- The particular product class needed by the counterexample is an actual cycle. -/
def explicitCircleFamily : LocallyFiniteK1 (Sigma CircleFamily) :=
  cycleClass C₀(Sigma CircleFamily, ℂ) circleSigmaCycle

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitPersistence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence of the explicit circle cycle in the actual graph union -/

noncomputable section

namespace CoarseAssembly

open Topology Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.explicitPersistenceComponent
attribute [local instance] OAI.CoarseAssembly.explicitPersistenceMetric
def explicitFiberStage (r : ℕ) (hr : 1 ≤ r) :
    LocallyFiniteK1 (Point FiberedUnion (r : ℝ)) :=
  pushforward (ripsFamilyMap fiberBoundaryBase r (explicitFiberLoops r hr)) explicitCircleFamily

def explicitFiberClass : KX1 FiberedUnion :=
  (coarsening FiberedUnion).of 1 (explicitFiberStage 1 le_rfl)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitBoundaryConclusion
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterexample with circle, filling and additivity inputs discharged -/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance explicitBoundaryMetric1_r64314b_1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitBoundaryMetric2_r64314b_1 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance explicitBoundaryMetric3_r64314b_1 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric4
def explicitBoundaryStage : LocallyFiniteK1 (Point BoundaryVertex 1) :=
  pushforward (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops)
    explicitCircleFamily

def explicitBoundaryClass : KX1 BoundaryVertex :=
  classAt 1 1 (by norm_num) explicitBoundaryStage

attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric5
attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric6
attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric7
def explicitCounterexampleClass : KX1 VertexUnion :=
  boundaryTotalCoarsening.homologyMap explicitBoundaryClass

def explicitRealFiberStage (r : ℝ) (hr : 1 ≤ r) :
    LocallyFiniteK1 (Point FiberedUnion r) :=
  pushforward (ripsFamilyMap fiberBoundaryBase r (realFiberLoops r hr)) explicitCircleFamily

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFiniteTail
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-tail invariance for the analytic Rips boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

attribute [local instance] OAI.CoarseAssembly.Rips.instSecondCountableTopologySubtypePreLpNatComplexMemAddSubgroupLpOfNatENNReal_solutions
theorem ControlledCycleFamily.boundary_eq_of_tail
    (c : ControlledCycleFamily Q r) (d : ControlledCycleFamily Q s)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s) (J : Finset ℕ)
    (htail : ∀ i, i ∉ J →
      ampleRipsOperator r (c.cycle i) (c.unital i) = ampleRipsOperator s (d.cycle i) (d.unital i)) :
    c.boundary o hr = d.boundary o hs := by
  let := separatedMetric o
  exact separatedFamilyBoundary_eq_of_tail o
    (fun i => ampleRipsOperator r (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator s (d.cycle i) (d.unital i))
    (c.bound + 4) (d.bound + 4) (by linarith [c.bound_nonneg]) (by linarith [d.bound_nonneg])
    (fun i => (ampleRipsOperator_norm_le r (c.cycle i) (c.unital i)).trans
      (by linarith [c.norm_le i]))
    (fun i => (ampleRipsOperator_norm_le s (d.cycle i) (d.unital i)).trans
      (by linarith [d.norm_le i]))
    (r + r) (s + s) (add_nonneg hr hr) (add_nonneg hs hs)
    (fun i => ampleRipsOperator_propagation r hr (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator_propagation s hs (d.cycle i) (d.unital i))
    (fun i => ampleRipsOperator_selfAdjoint r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_selfAdjoint s (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact s (d.cycle i) (d.unital i) (d.selfAdjoint i))
    J htail

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

def matrixWord : List Mat3 → Mat3
  | [] => matOne
  | a::as => matMul a (matrixWord as)

def generator2 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 0, 1]
def generator3 : Mat3 := [1, 0, 1, 0, 1, 0, 0, 0, 1]
def generator4 : Mat3 := [1, 0, 0, -1, 1, 0, 0, 0, 1]
def generator5 : Mat3 := [1, 0, 0, 1, 1, 0, 0, 0, 1]
def generator6 : Mat3 := [1, 0, 0, 0, 1, -1, 0, 0, 1]
def generator7 : Mat3 := [1, 0, 0, 0, 1, 1, 0, 0, 1]
def generator8 : Mat3 := [1, 0, 0, 0, 1, 0, -1, 0, 1]
def generator9 : Mat3 := [1, 0, 0, 0, 1, 0, 1, 0, 1]
def generator10 : Mat3 := [1, 0, 0, 0, 1, 0, 0, -1, 1]
def generator11 : Mat3 := [1, 0, 0, 0, 1, 0, 0, 1, 1]

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate

def gramPolyRow (a : Mat3) (r : List ℤ) : Poly Mat3 :=
  (basis.zip r).map (fun q => (matMul (matInv a) q.1, -10*q.2))

def rootPairs : List (Mat3 × List ℤ) := basis.zip columns

section Operator
variable {A : Type*} [Ring A] [StarRing A]

def gramValue (f : Mat3 → A) : A :=
  (rootPairs.map (fun p =>
    (rootPairs.map (fun q => dot p.2 q.2 • (star (f p.1) * f q.1))).sum)).sum

end Operator
end NuclearUltrapower.SOS
end

end OAI
end


