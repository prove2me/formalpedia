-- Prove2me | Definitions.Def_OAIQ229C024
-- name    : OAIQ229C024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:24.179038+00:00
-- url     : https://prove2.me/theorems/1d290e4d-cf41-43a6-aba2-509fd03396b2
-- title:
--   Definitions bundle OAIQ229C024 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 7 definitions and 25 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.sampledFiniteSum_head_tail`, `OAI.CoarseAssembly.Analytic.sampledFiniteSum_rotate`, `OAI.CoarseAssembly.Analytic.sigmaComplementCycle`, `OAI.CoarseAssembly.Analytic.sigmaCycle`, `OAI.CoarseAssembly.Analytic.sigmaCycle_directSum`, `OAI.CoarseAssembly.Analytic.zeroRepresentationCycle`, `OAI.CoarseAssembly.HexagonalBoundaryWalks.fiberWalk`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_AmpleRipsFamily`, `CoarseAssembly_BlockIsometryRelations`, `CoarseAssembly_BoundaryWalks`, `CoarseAssembly_CoefficientDecomposition`, `CoarseAssembly_CoefficientInclusion`, `CoarseAssembly_EmbeddingBoundaryComparison`, `CoarseAssembly_EmbeddingTransition`, `CoarseAssembly_FamilyCoefficientEmbedding`, `CoarseAssembly_FamilyDecomposition`, `CoarseAssembly_LocalizationUniformEstimate`, `CoarseAssembly_MultiplierOrthogonalEmbeddings`, `CoarseAssembly_PartitionIntertwining`, `CoarseAssembly_RipsLocalization`, `CoarseAssembly_RipsUnitaryLocalization`, `CoarseAssembly_SampledHomotopy`, `CoarseAssembly_SampledHomotopyDecomposition`, `CoarseAssembly_SampledHomotopyEstimates`, `CoarseAssembly_SeparatedFamilyPerturbation`, `CoarseAssembly_SigmaCycle`, `CoarseAssembly_SigmaCycleRestriction`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C016`, `OAIQ229C017`, `OAIQ229C018` and `OAIQ229C019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C028` and `OAIQ229C029`; the statement `OAI_CoarseAssembly_provedKazhdanInput`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
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
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
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
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C016
import Definitions.Def_OAIQ229C017
import Definitions.Def_OAIQ229C018
import Definitions.Def_OAIQ229C019

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsLocalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The spatial localization of a unital finite-Rips Fredholm cycle -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)

theorem ripsSpatialOperator_propagation (hr : 0 ≤ r) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : PropagationLE (r + r) (ripsSpatialOperator r c hπ) :=
  localizedSpatialOperator_propagation _ _ (representedSqrt_adjoint r c) r hr
    (representedSqrt_disjoint r c) c.operator

theorem ripsSpatialOperator_norm_le (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : ‖ripsSpatialOperator r c hπ‖ ≤ ‖c.operator‖ + 2 :=
  localizedSpatialOperator_norm_le _ _ _

theorem ripsSpatialOperator_selfAdjoint (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsSelfAdjoint (ripsSpatialOperator r c hπ) :=
  localizedSpatialOperator_selfAdjoint _ _ _ hF

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AmpleRipsFamily
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial representatives for finite-Rips families on the fixed ample module

The source Hilbert spaces may vary with the component. Each is embedded
isometrically into ℓ²(ℕ, ℂ), and the operator is extended by the identity.
The compact square defects give one whole-union boundary class.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ampleRipsOperator_norm_le (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : ‖ampleRipsOperator r c hπ‖ ≤ ‖c.operator‖ + 4 := by
  exact (coefficientExtension_norm_le _ _).trans
    (by linarith [ripsSpatialOperator_norm_le r c hπ])

theorem ampleRipsOperator_propagation (r : ℝ) (hr : 0 ≤ r)
    (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    PropagationLE (r + r) (ampleRipsOperator r c hπ) :=
  coefficientExtension_propagation _ (add_nonneg hr hr) (ripsSpatialOperator_propagation r hr c hπ)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EmbeddingTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The partial isometry comparing two Hilbert-space embeddings -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rationalBoundaryUnitary_isometricExtension (V : E →ₗᵢ[ℂ] H)
    (F : E →L[ℂ] E) (hF : IsSelfAdjoint F) :
    (Analytic.rationalBoundaryUnitary (isometricExtension V F)
      (isometricExtension_selfAdjoint V F hF) : H →L[ℂ] H) =
        1 + operatorConjugation V ((Analytic.rationalBoundaryUnitary F hF : E →L[ℂ] E) - 1) :=
  (Analytic.nonunital_rationalBoundaryUnitary (operatorConjugationHom V) F hF).symm

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EmbeddingBoundaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality of Roe boundary classes from two embeddings of one operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic OperatorKTheory

variable {X E H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem multiplierBoundaryUnitary_embedding (V : E →ₗᵢ[ℂ] Module X H)
    (S : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hFV : F.val = isometricExtension V S) :
    (multiplierBoundaryUnitary F hF : Operator X H) - 1 =
      operatorConjugation V ((rationalBoundaryUnitary S hS : E →L[ℂ] E) - 1) := by
  have hm := map_rationalBoundaryUnitary
    (multiplierAlgebra (X := X) (H := H)).subtype F hF
  change (multiplierBoundaryUnitary F hF : Operator X H) =
    (rationalBoundaryUnitary F.val (hF.map (multiplierAlgebra (X := X) (H := H)).subtype) :
      Operator X H) at hm
  simp only [hFV] at hm
  rw [rationalBoundaryUnitary_isometricExtension V S hS] at hm
  rw [hm, add_sub_cancel_left]

/-- Two embeddings of the same operator give the same class whenever their
transition is a Roe multiplier. Coefficient embeddings satisfy this via propagation zero. -/
theorem multiplierBoundaryClass_embedding
    (V W : E →ₗᵢ[ℂ] Module X H) (S : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (F G : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hFV : F.val = isometricExtension V S) (hGW : G.val = isometricExtension W S)
    (hVW : RoeMultiplier (embeddingTransition V W)) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd := by
  let T : multiplierAlgebra (X := X) (H := H) := ⟨embeddingTransition V W, hVW⟩
  let u := rationalBoundaryUnitary F hF
  let v := rationalBoundaryUnitary G hG
  let a := (rationalBoundaryUnitary S hS : E →L[ℂ] E) - 1
  have hu : (u : multiplierAlgebra (X := X) (H := H)).val - 1 = operatorConjugation V a :=
    multiplierBoundaryUnitary_embedding V S hS F hF hFV
  have hv : (v : multiplierAlgebra (X := X) (H := H)).val - 1 = operatorConjugation W a :=
    multiplierBoundaryUnitary_embedding W S hS G hG hGW
  have hT : T * star T * T = T := by
    apply Subtype.ext
    exact embeddingTransition_partial V W
  have hl : (star T * T) * ((u : multiplierAlgebra (X := X) (H := H)) - 1) =
      (u : multiplierAlgebra (X := X) (H := H)) - 1 := by
    apply Subtype.ext
    change (star (embeddingTransition V W) * embeddingTransition V W) *
      ((u : multiplierAlgebra (X := X) (H := H)).val - 1) =
        (u : multiplierAlgebra (X := X) (H := H)).val - 1
    rw [hu]
    exact embeddingTransition_support_left V W a
  have hr : ((u : multiplierAlgebra (X := X) (H := H)) - 1) * (star T * T) =
      (u : multiplierAlgebra (X := X) (H := H)) - 1 := by
    apply Subtype.ext
    change ((u : multiplierAlgebra (X := X) (H := H)).val - 1) *
      (star (embeddingTransition V W) * embeddingTransition V W) =
        (u : multiplierAlgebra (X := X) (H := H)).val - 1
    rw [hu]
    exact embeddingTransition_support_right V W a
  have he : (v : multiplierAlgebra (X := X) (H := H)) =
      1 + T * ((u : multiplierAlgebra (X := X) (H := H)) - 1) * star T := by
    apply Subtype.ext
    change (v : multiplierAlgebra (X := X) (H := H)).val =
      1 + embeddingTransition V W * ((u : multiplierAlgebra (X := X) (H := H)).val - 1) *
        star (embeddingTransition V W)
    rw [hu, embeddingTransition_conjugation]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hv)
  let φ := (multiplierAlgebra (X := X) (H := H)).subtype
  exact relativeClass_partialIsometry (hS := algebra_isClosed)
    (algebra (X := X) (H := H)) φ continuous_subtype_val
    (fun b c hc => b.property ⟨c, hc⟩) T hT u v hl hr he
    (multiplierBoundaryUnitary_sub_one_mem F hF hFd)
    (multiplierBoundaryUnitary_sub_one_mem G hG hGd)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyCoefficientEmbedding
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single source Hilbert sum for all choices of ample coefficients -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem familyEmbeddingTransition_propagation (V W : ∀ i, E i →ₗᵢ[ℂ] H)
    [PseudoMetricSpace (Sigma Q)] :
    PropagationLE 0 (embeddingTransition (familyCoefficientIsometry (Q := Q) V)
      (familyCoefficientIsometry W)) := by
  intro x y hxy
  have hne : x ≠ y := by rintro rfl; simp at hxy
  rcases x with ⟨i, x⟩
  ext h
  change familyCoefficientIsometry W
    ((familyCoefficientIsometry V).toContinuousLinearMap.adjoint (lp.single 2 y h)) ⟨i, x⟩ = 0
  rw [familyCoefficientIsometry_apply, familyCoefficientIsometry_adjoint_apply]
  simp [lp.single_apply, hne]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsUnitaryLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary equivalence commutes with finite-Rips localization -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DiscreteRoe

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem partitionIsometry_apply (a : X → E →L[ℂ] E)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (v : E) (x : X) :
    partitionIsometry a ha v x = a x v := by
  exact DFunLike.congr_fun (coordinate_partitionMap a x) v

end DiscreteRoe

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite localization respects reducing isometric intertwiners -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem localizedSpatialOperator_apply (a : X → E →L[ℂ] E)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (F : E →L[ℂ] E)
    (v : Module X E) (x : X) :
    localizedSpatialOperator a ha F v x =
      v x + a x ((partitionCompression a F - 1) (∑ y, (a y).adjoint (v y))) := by
  change v x + partitionIsometry a ha
    ((partitionCompression a F - 1) ((partitionIsometry a ha).toContinuousLinearMap.adjoint v)) x = _
  rw [partitionIsometry_apply, partitionIsometry_toContinuousLinearMap, partitionMap_adjoint_apply]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal decompositions lifted to the spatial vertex modules -/

noncomputable section

namespace CoarseAssembly

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DiscreteRoe

variable {X : Type*} [DecidableEq X]

omit [CompleteSpace F] [DecidableEq X] in
theorem coefficientIsometry_orthogonal (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.adjoint.comp
      (coefficientIsometry W).toContinuousLinearMap = 0 := by
  ext v x
  change (coefficientIsometry V).toContinuousLinearMap.adjoint (coefficientIsometry W v) x = 0
  rw [coefficientIsometry_adjoint_apply, coefficientIsometry_apply]
  exact DFunLike.congr_fun hVW (v x)

end DiscreteRoe

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockIsometryRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing decompositions and intertwiners on bounded Hilbert sums -/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} {E F G : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

omit [∀ i, CompleteSpace (F i)] in
theorem blockIsometry_orthogonal (V : ∀ i, E i →ₗᵢ[ℂ] G i) (W : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hVW : ∀ i, (V i).toContinuousLinearMap.adjoint.comp (W i).toContinuousLinearMap = 0) :
    (blockIsometry V).toContinuousLinearMap.adjoint.comp (blockIsometry W).toContinuousLinearMap = 0 := by
  ext v i
  change (blockIsometry V).toContinuousLinearMap.adjoint (blockIsometry W v) i = 0
  rw [blockIsometry_adjoint_coordinate, blockIsometry_apply]
  exact DFunLike.congr_fun (hVW i) (v i)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary walks and their canonical lifts

Depth-zero fibers are singletons, so every edge of the actual boundary
subgraph has its unique lift. The walk construction and charge comparison
here leave only the explicit hexagonal boundary walk to be supplied.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

def HexagonalBoundaryWalks.fiberWalk (w : HexagonalBoundaryWalks)
    (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    (fiberedGraph S t j).Walk (fiberBoundaryBase j) (fiberBoundaryBase j) :=
  (w.walk j).map (boundaryFiberHom S t j)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ample coefficient transport commutes with vertex inclusion -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X Y E H : Type*} [DecidableEq X] [DecidableEq Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq X] [DecidableEq Y] in
theorem coefficientIsometry_inclusion (V : E →ₗᵢ[ℂ] H) (e : X ↪ Y) :
    (coefficientIsometry (X := Y) V).comp (inclusionIsometry (H := E) e) =
      (inclusionIsometry (H := H) e).comp (coefficientIsometry (X := X) V) := by
  apply DFunLike.ext
  intro v
  apply lp.ext
  funext y
  change V (inclusionVector e v y) = inclusionVector e (coefficientIsometry V v) y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [inclusionVector_apply, inclusionVector_apply, coefficientIsometry_apply]
  · rw [inclusionVector_zero e _ _ hy, inclusionVector_zero e _ _ hy, map_zero]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierOrthogonalEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Addition of actual Roe boundaries supported in orthogonal images -/

noncomputable section

namespace CoarseAssembly

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DiscreteRoe

open Analytic OperatorKTheory

variable {X : Type*} [DecidableEq X] [PseudoMetricSpace X]

theorem multiplierBoundaryUnitary_eq_raw
    (T : multiplierAlgebra (X := X) (H := H)) (hT : IsSelfAdjoint T) :
    (multiplierBoundaryUnitary T hT : Operator X H) =
      (rationalBoundaryUnitary T.val (hT.map (multiplierAlgebra (X := X) (H := H)).subtype) :
        Operator X H) :=
  map_rationalBoundaryUnitary (multiplierAlgebra (X := X) (H := H)).subtype T hT

/-- The complementary target summand carries the identity; the two supported
boundary classes therefore add in the actual Roe K₁ group. -/
theorem multiplierBoundaryClass_orthogonalEmbeddings
    (V : E →ₗᵢ[ℂ] Module X H) (W : F →ₗᵢ[ℂ] Module X H)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (T L R : multiplierAlgebra (X := X) (H := H))
    (hT : IsSelfAdjoint T) (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R)
    (hTd : T.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hLd : L.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hRd : R.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hLV : L.val = isometricExtension V A) (hRW : R.val = isometricExtension W B)
    (hTVW : T.val = 1 + operatorConjugation V (A - 1) + operatorConjugation W (B - 1)) :
    multiplierBoundaryClass T hT hTd =
      multiplierBoundaryClass L hL hLd + multiplierBoundaryClass R hR hRd := by
  let φ := operatorConjugationHom V
  let ψ := operatorConjugationHom W
  have horth : ∀ a b, φ a * ψ b = 0 := operatorConjugation_orthogonal V W hVW
  let σ := nonunitalOrthogonalSumHom φ ψ horth
  have ht : T.val = nonunitalIdentityExtension σ (A, B) := by
    change T.val = 1 + (operatorConjugation V (A - 1) + operatorConjugation W (B - 1))
    simpa only [add_assoc] using hTVW
  have huT := multiplierBoundaryUnitary_eq_raw T hT
  simp only [ht] at huT
  have hprod := rationalBoundaryUnitary_orthogonalExtension φ ψ horth A B hA hB
  have huL : (multiplierBoundaryUnitary L hL : Operator X H) =
      (nonunitalUnitaryExtension φ (rationalBoundaryUnitary A hA) : Operator X H) := by
    have h := multiplierBoundaryUnitary_embedding V A hA L hL hLV
    change (multiplierBoundaryUnitary L hL : Operator X H) =
      1 + operatorConjugation V ((rationalBoundaryUnitary A hA : E →L[ℂ] E) - 1)
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  have huR : (multiplierBoundaryUnitary R hR : Operator X H) =
      (nonunitalUnitaryExtension ψ (rationalBoundaryUnitary B hB) : Operator X H) := by
    have h := multiplierBoundaryUnitary_embedding W B hB R hR hRW
    change (multiplierBoundaryUnitary R hR : Operator X H) =
      1 + operatorConjugation W ((rationalBoundaryUnitary B hB : F →L[ℂ] F) - 1)
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  have hu : multiplierBoundaryUnitary T hT = multiplierBoundaryUnitary L hL *
      multiplierBoundaryUnitary R hR := by
    apply Subtype.ext
    rw [huT]
    have hp := congrArg (fun u : unitary (Operator X H) => u.val) hprod
    change _ = (multiplierBoundaryUnitary L hL : Operator X H) *
      (multiplierBoundaryUnitary R hR : Operator X H)
    rw [huL, huR]
    exact hp
  have h := relativeClass_mul (hS := algebra_isClosed) (algebra (X := X) (H := H))
    (multiplierBoundaryUnitary L hL) (multiplierBoundaryUnitary R hR)
    (multiplierBoundaryUnitary_sub_one_mem L hL hLd)
    (multiplierBoundaryUnitary_sub_one_mem R hR hRd)
  simpa only [multiplierBoundaryClass, ← hu] using h

end DiscreteRoe
end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal decomposition of a whole coefficient family -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E F G : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
  [∀ i, CompleteSpace (F i)] in
theorem familyCoefficientIsometry_orthogonal
    (U : ∀ i, G i →ₗᵢ[ℂ] H) (L : ∀ i, E i →ₗᵢ[ℂ] G i) (R : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hLR : ∀ i, (L i).toContinuousLinearMap.adjoint.comp (R i).toContinuousLinearMap = 0) :
    (familyCoefficientIsometry (Q := Q) (fun i => (U i).comp (L i))).toContinuousLinearMap.adjoint.comp
      (familyCoefficientIsometry (fun i => (U i).comp (R i))).toContinuousLinearMap = 0 := by
  have h := isometry_comp_orthogonal (familyCoefficientIsometry (Q := Q) U)
    (blockIsometry (fun i => coefficientIsometry (X := Q i) (L i)))
    (blockIsometry (fun i => coefficientIsometry (X := Q i) (R i)))
    (blockIsometry_orthogonal _ _ (fun i => coefficientIsometry_orthogonal (L i) (R i) (hLR i)))
  simpa only [familyCoefficientIsometry_comp] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LocalizationUniformEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A component-independent estimate for representation-varying localization -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [DecidableEq X] [CompleteSpace H] in
theorem constantBlock_sub (F G : H →L[ℂ] H) :
    constantBlock (X := X) F - constantBlock G = constantBlock (F - G) := by
  ext v x
  rfl

theorem localizedSpatialOperator_eq_sandwich (a : X → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    localizedSpatialOperator a ha F =
      1 + operatorSandwich (partitionMap a) (partitionCompression a F - 1) := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledHomotopy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite samples of an analytic homotopy

The inactive summands are degenerate character cycles on the same Hilbert
space. Thus the ambient countable Hilbert sum does not depend on the samples.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem sampledFiniteSum_unital (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (hπ : ∀ t, h.representation t 1 = 1) :
    (sampledFiniteSum h χ N τ C hC hF).representation 1 = 1 :=
  finiteActiveCycle_unital _ _ _ _ _ _ (fun j => sampledCycle_unital h χ N τ j hπ)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledHomotopyDecomposition
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.intervalGrid_finish _root_.OAI.CoarseAssembly.Analytic.intervalGrid_start _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint and interior decompositions of finite homotopy samples -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def sampledFiniteSum_head_tail (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) :
    (h.eval (τ 0)).IsDirectSum
      (sampledFiniteSum h χ N (fun j => τ (j + 1)) C hC hF)
      (sampledFiniteSum h χ (N + 1) τ C hC hF) where
  left := summandIsometry (fun _ => h.space) 0
  right := tailInsert (fun _ => h.space)
  orthogonal := head_tail_orthogonal _
  exhaustive := head_tail_exhaustive _
  representation_eq a := by
    change blockOperator (fun j => (if j < N + 1 then h.representation (τ j) else
      characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a)
      ‖a‖ (norm_nonneg _) _ = _
    erw [blockOperator_head_tail]
    simp only [Nat.add_lt_add_iff_right, Nat.zero_lt_succ, ite_true, if_true]
    rfl
  operator_eq := by
    change blockOperator (fun j => if j < N + 1 then h.operator (τ j) else 1)
      C (zero_le_one.trans hC) _ = _
    erw [blockOperator_head_tail]
    simp only [Nat.add_lt_add_iff_right, Nat.zero_lt_succ, ite_true, if_true]
    rfl

def sampledFiniteSum_rotate (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) :
    (sampledFiniteSum h χ (N + 1) (lastEndpointFirst N τ) C hC hF).UnitaryEquivalent
      (sampledFiniteSum h χ (N + 1) (fun j => τ (j + 1)) C hC hF) where
  unitary := repeatedReindexEquiv h.space (rotatePrefix N)
  representation_eq a := by
    symm
    change operatorConjugation (repeatedReindexEquiv h.space (rotatePrefix N)).toLinearIsometry
      (blockOperator (fun j => (if j < N + 1 then h.representation (lastEndpointFirst N τ j) else
        characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a)
        ‖a‖ (norm_nonneg _) _) = _
    erw [blockOperator_reindex]
    ext x j
    change (sampledCycle h χ (N + 1) (lastEndpointFirst N τ) ((rotatePrefix N).symm j)).representation a (x j) =
      (sampledCycle h χ (N + 1) (fun j => τ (j + 1)) j).representation a (x j)
    by_cases hj : j < N
    · rw [rotatePrefix_inverse_lt N j hj]
      simp [sampledCycle, lastEndpointFirst, Nat.lt_add_one_of_lt hj, hj]
      rfl
    · by_cases he : j = N
      · subst j
        simp [sampledCycle, lastEndpointFirst]
        rfl
      · have hgt : N < j := by omega
        rw [rotatePrefix_inverse_gt N j hgt]
        simp [sampledCycle, show ¬j < N + 1 by omega]
        rfl
  operator_eq := by
    symm
    change operatorConjugation (repeatedReindexEquiv h.space (rotatePrefix N)).toLinearIsometry
      (blockOperator (fun j => if j < N + 1 then h.operator (lastEndpointFirst N τ j) else 1)
        C (zero_le_one.trans hC) _) = _
    erw [blockOperator_reindex]
    ext x j
    change (sampledCycle h χ (N + 1) (lastEndpointFirst N τ) ((rotatePrefix N).symm j)).operator (x j) =
      (sampledCycle h χ (N + 1) (fun j => τ (j + 1)) j).operator (x j)
    by_cases hj : j < N
    · rw [rotatePrefix_inverse_lt N j hj]
      simp [sampledCycle, lastEndpointFirst, Nat.lt_add_one_of_lt hj, hj]
      rfl
    · by_cases he : j = N
      · subst j
        simp [sampledCycle, lastEndpointFirst]
        rfl
      · have hgt : N < j := by omega
        rw [rotatePrefix_inverse_gt N j hgt]
        simp [sampledCycle, show ¬j < N + 1 by omega]
        rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledHomotopyEstimates
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform norm estimates for arbitrarily many finite samples -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem sampledFiniteSum_operator_sub_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ j, j < N → ‖h.operator (τ j) - h.operator (σ j)‖ ≤ δ) :
    ‖(show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N τ C hC hF).operator) -
      (show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N σ C hC hF).operator)‖ ≤ δ := by
  apply blockOperator_dist_le (hε := hδ)
  intro j
  change ‖(if j < N then h.operator (τ j) else 1) -
    (if j < N then h.operator (σ j) else 1)‖ ≤ δ
  by_cases hj : j < N
  · simpa only [ite_eq_left hj] using hnear j hj
  · simpa only [ite_eq_right hj, sub_self, norm_zero] using hδ

theorem sampledFiniteSum_representation_sub_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ σ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (a : A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ j, j < N → ‖h.representation (τ j) a - h.representation (σ j) a‖ ≤ δ) :
    ‖(show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N τ C hC hF).representation a) -
      (show End (repeatedHilbert h.space) from (sampledFiniteSum h χ N σ C hC hF).representation a)‖ ≤ δ := by
  apply blockOperator_dist_le (hε := hδ)
  intro j
  change ‖(if j < N then h.representation (τ j) else
      characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a -
    (if j < N then h.representation (σ j) else
      characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) a‖ ≤ δ
  by_cases hj : j < N
  · simpa only [ite_eq_left hj] using hnear j hj
  · simpa only [ite_eq_right hj, sub_self, norm_zero] using hδ

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedFamilyPerturbation
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_adjoint_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.familyCoefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply _root_.OAI.CoarseAssembly.DiscreteRoe.rowRestriction_apply _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact changes on components give Roe perturbations on the whole union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, Fintype (V i)] in
theorem diagonalFamily_sub_mem_roe (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAB : ∀ i, IsCompactOperator (A i - B i)) :
    letI := separatedMetric o
    diagonalFamily A C hC hA - diagonalFamily B D hD hB ∈ algebra (X := Sigma V) (H := H) := by
  let := separatedMetric o
  have hn : ∀ i, ‖A i - B i‖ ≤ C + D := fun i =>
    (norm_sub_le _ _).trans (add_le_add (hA i) (hB i))
  rw [diagonalFamily_sub_eq A B C D hC hD hA hB (C + D) (add_nonneg hC hD) hn]
  let Q := diagonalFamily (fun i => A i - B i) (C + D) (add_nonneg hC hD) hn
  have hQp : PropagationLE (max r s) Q := by
    apply diagonalFamily_propagation o
    intro i
    have hneg : PropagationLE s (-B i) := by
      convert (hq i).smul (-1 : ℂ) using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      simp
    simpa only [sub_eq_add_neg] using (hp i).add hneg
  have hQc : CompactEntries Q := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      rw [entry_diagonalFamily_same]
      exact compact_entries_of_compact (hAB i) x y
    · rw [entry_diagonalFamily_ne _ _ _ _ hij]
      exact isCompactOperator_zero
  have hQs : IsSelfAdjoint Q :=
    diagonalFamily_selfAdjoint _ _ _ _ (fun i =>
      @IsSelfAdjoint.sub (Operator (V i) H) inferInstance inferInstance _ _ (hAs i) (hBs i))
  exact generator_mem ⟨⟨max r s, le_trans hr (le_max_left _ _), hQp⟩, hQc,
    by rwa [hQs.star_eq]⟩

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycle
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling uniformly bounded normalized Fredholm cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped ZeroAtInfty Topology

variable {H : HilbertSpace}

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
variable (c : ∀ j, OddCycle C(Y j, ℂ))
variable (M : ℝ) (hM : 0 ≤ M) (hF : ∀ j, ‖(c j).operator‖ ≤ M)

theorem sigmaCycleOperator_commutator (f : C₀(Sigma Y, ℂ)) :
    IsCompactOperator (sigmaCycleOperator Y c M hM hF * sigmaCycleRepresentation Y c f -
      sigmaCycleRepresentation Y c f * sigmaCycleOperator Y c M hM hF) := by
  have he : sigmaCycleOperator Y c M hM hF * sigmaCycleRepresentation Y c f -
      sigmaCycleRepresentation Y c f * sigmaCycleOperator Y c M hM hF =
      CoarseAssembly.blockOperator (sigmaCommutatorBlocks Y c f) ((2 * M) * ‖f‖)
        (by positivity) (sigmaCommutator_uniform_bound Y c M hM hF f) := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    rfl
  rw [he]
  exact blockSum_compact (cycleHilbertFamily Y c) (sigmaCommutatorBlocks Y c f)
    ((2 * M) * ‖f‖) (by positivity) (sigmaCommutator_uniform_bound Y c M hM hF f)
    (fun j => (c j).commutator_compact _) (sigmaCommutator_norm_tendsto Y c M hM hF f)

/-- A countable family of normalized cycles gives an actual locally finite cycle. -/
def sigmaCycle (hself : ∀ j, IsSelfAdjoint (c j).operator)
    (hsq : ∀ j, (c j).operator * (c j).operator = 1) : OddCycle C₀(Sigma Y, ℂ) where
  space := countableHilbertSpace (cycleHilbertFamily Y c)
  representation := sigmaCycleRepresentation Y c
  operator := sigmaCycleOperator Y c M hM hF
  commutator_compact := sigmaCycleOperator_commutator Y c M hM hF
  square_compact f := by
    rw [sigmaCycleOperator_sq Y c M hM hF hsq, sub_self, zero_mul]
    exact isCompactOperator_zero
  adjoint_compact f := by
    rw [(sigmaCycleOperator_selfAdjoint Y c M hM hF hself).star_eq, sub_self, zero_mul]
    exact isCompactOperator_zero

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycleRestriction
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coordinates of an actual countable Fredholm cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {A : Type} [NonUnitalCStarAlgebra A]

def zeroRepresentationCycle (H : HilbertSpace) (F : End H) : OddCycle A where
  space := H
  representation := 0
  operator := F
  commutator_compact _ := by simp; exact isCompactOperator_zero
  square_compact _ := by simp; exact isCompactOperator_zero
  adjoint_compact _ := by simp; exact isCompactOperator_zero

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, T2Space (Y j)]

variable (c : ∀ j, OddCycle C(Y j, ℂ))
variable (M : ℝ) (hM : 0 ≤ M) (hF : ∀ j, ‖(c j).operator‖ ≤ M)

theorem sigmaCycleRepresentation_extension (j : ℕ) (f : C₀(Y j, ℂ)) :
    sigmaCycleRepresentation Y c
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) =
      operatorConjugation (summandIsometry (cycleHilbertFamily Y c) j)
        ((c j).representation (compactFunctionForget f)) := by
  unfold operatorConjugation
  rw [summandIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  change (c k).representation (sigmaFunctionRestriction Y k
    (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f)) (x k) =
      lp.single (E := fun k => (c k).space) 2 j
        ((c j).representation (compactFunctionForget f) (x j)) k
  by_cases hjk : j = k
  · subst k
    rw [sigmaRestriction_extension_same]
    simp
  · rw [sigmaRestriction_extension_ne Y j k hjk, map_zero]
    simp [Pi.single_eq_of_ne (Ne.symm hjk)]

def sigmaComplementCycle (j : ℕ) : OddCycle C₀(Y j, ℂ) :=
  zeroRepresentationCycle (complementHilbertSpace (cycleHilbertFamily Y c) j)
    (complementBlockOperator (cycleHilbertFamily Y c) (fun k => (c k).operator) M hM hF j)

def sigmaCycle_directSum (hself : ∀ j, IsSelfAdjoint (c j).operator)
    (hsq : ∀ j, (c j).operator * (c j).operator = 1) (j : ℕ) :
    ((c j).precomp compactFunctionForget).IsDirectSum (sigmaComplementCycle Y c M hM hF j)
      ((sigmaCycle Y c M hM hF hself hsq).precomp
        (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j))) where
  left := summandIsometry (cycleHilbertFamily Y c) j
  right := complementIsometry (cycleHilbertFamily Y c) j
  orthogonal := summand_complement_orthogonal (cycleHilbertFamily Y c) j
  exhaustive := summand_complement_exhaustive (cycleHilbertFamily Y c) j
  representation_eq f := by
    change sigmaCycleRepresentation Y c
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) =
        operatorConjugation (summandIsometry (cycleHilbertFamily Y c) j)
          ((c j).representation (compactFunctionForget f)) +
        operatorConjugation (complementIsometry (cycleHilbertFamily Y c) j)
          (0 : End (complementHilbertSpace (cycleHilbertFamily Y c) j))
    rw [sigmaCycleRepresentation_extension]
    simp [operatorConjugation]
  operator_eq := blockOperator_decomposition (cycleHilbertFamily Y c)
    (fun k => (c k).operator) M hM hF j

end CoarseAssembly.Analytic

end

end OAI
end


