-- Prove2me | Definitions.Def_OAIQ229C028
-- name    : OAIQ229C028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T12:15:32.509894+00:00
-- url     : https://prove2.me/theorems/b033756d-afbe-4510-9b9e-0be6ce5e671c
-- title:
--   Definitions bundle OAIQ229C028 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 3 definitions and 7 theorems. The definitions and types are `OAI.CoarseAssembly.Rips.BoundedFamilyHomotopy.sample`, `OAI.CoarseAssembly.fiberLoopsOne`, `OAI.CoarseAssembly.realFiberLoops`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_AmpleRipsFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/AmpleRipsFamily.lean), [`CoarseAssembly_BoundaryLoopMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/BoundaryLoopMaps.lean), [`CoarseAssembly_BoundedFamilyHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/BoundedFamilyHomotopy.lean), [`CoarseAssembly_FamilyBoundaryAddition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FamilyBoundaryAddition.lean), [`CoarseAssembly_FamilyEmbeddingIndependence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/FamilyEmbeddingIndependence.lean), [`CoarseAssembly_LocalizationUniformEstimate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/LocalizationUniformEstimate.lean), [`CoarseAssembly_PartitionIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/PartitionIntertwining.lean), [`CoarseAssembly_RipsInclusionNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsInclusionNaturality.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C024`, `OAIQ229C025`, `OAIQ229C026` and `OAIQ229C027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C032`, `OAIQ229C033` and `OAIQ229C034`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
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
import Definitions.Def_OAIQ229C024
import Definitions.Def_OAIQ229C025
import Definitions.Def_OAIQ229C026
import Definitions.Def_OAIQ229C027

section
-- module Solutions.Q229_CA.CoarseAssembly_AmpleRipsFamily
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem ampleRipsOperator_selfAdjoint (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsSelfAdjoint (ampleRipsOperator r c hπ) :=
  coefficientExtension_selfAdjoint _ _ (ripsSpatialOperator_selfAdjoint r c hπ hF)

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryLoopMaps
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same boundary family maps to the filled base and detected total space

The source class is defined on the actual boundary Rips complex. Its base
image is identified with the previously constructed filled loop family.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric1
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric3
local instance boundaryLoopMetric4_rb7a36c_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric6
def realFiberLoops (r : ℝ) (hr : 1 ≤ r) (j : ℕ) :
    C(WindingCircle, Point (FiberVertex j) r) := by
  exact loopCircle (walkPath (le_trans (by norm_num) hr)
    (fun x y h => by
      have he := graphEdgeBound (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j)
        1 le_rfl x y h
      have he' : dist x y ≤ 1 := by simpa only [Nat.cast_one] using he
      exact he'.trans hr)
    (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit j))

def fiberLoopsOne := realFiberLoops 1 le_rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyEmbeddingIndependence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ample coefficient choices do not affect a whole-family Roe boundary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- This compares whole-union classes directly, without passing to component K₁ classes. -/
theorem coefficientFamilyBoundary_independent (o : ∀ i, Q i)
    (A : ∀ i, Operator (Q i) (E i)) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
    (hs : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i))))
    (V W : ∀ i, E i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    coefficientFamilyBoundary o A C hC hA r hr hp hs hsq V =
      coefficientFamilyBoundary o A C hC hA r hr hp hs hsq W := by
  let := separatedMetric o
  let AV := fun i => coefficientExtension (V i) (A i)
  let AW := fun i => coefficientExtension (W i) (A i)
  have hC' : 0 ≤ C + 2 := by linarith
  have hAV : ∀ i, ‖AV i‖ ≤ C + 2 := fun i =>
    (coefficientExtension_norm_le (V i) (A i)).trans (by linarith [hA i])
  have hAW : ∀ i, ‖AW i‖ ≤ C + 2 := fun i =>
    (coefficientExtension_norm_le (W i) (A i)).trans (by linarith [hA i])
  have hpV : ∀ i, PropagationLE r (AV i) := fun i =>
    coefficientExtension_propagation (V i) hr (hp i)
  have hpW : ∀ i, PropagationLE r (AW i) := fun i =>
    coefficientExtension_propagation (W i) hr (hp i)
  have hsV : ∀ i, IsSelfAdjoint (AV i) := fun i =>
    coefficientExtension_selfAdjoint (V i) (A i) (hs i)
  have hsW : ∀ i, IsSelfAdjoint (AW i) := fun i =>
    coefficientExtension_selfAdjoint (W i) (A i) (hs i)
  have hsqV : ∀ i, IsCompactOperator (AV i * AV i - (1 : Operator (Q i) H)) := fun i =>
    coefficientExtension_square_compact (V i) (A i) (hsq i)
  have hsqW : ∀ i, IsCompactOperator (AW i * AW i - (1 : Operator (Q i) H)) := fun i =>
    coefficientExtension_square_compact (W i) (A i) (hsq i)
  let F := separatedFamilyMultiplier (H := H) o AV (C + 2) hC' hAV r hr hpV
  let G := separatedFamilyMultiplier (H := H) o AW (C + 2) hC' hAW r hr hpW
  have hFs := separatedFamilyMultiplier_selfAdjoint o AV (C + 2) hC' hAV r hr hpV hsV
  have hGs := separatedFamilyMultiplier_selfAdjoint o AW (C + 2) hC' hAW r hr hpW hsW
  have hFd := diagonalFamily_square_mem_roe o AV (C + 2) hC' hAV r hr hpV hsV hsqV
  have hGd := diagonalFamily_square_mem_roe o AW (C + 2) hC' hAW r hr hpW hsW hsqW
  change multiplierBoundaryClass F hFs hFd = multiplierBoundaryClass G hGs hGd
  exact multiplierBoundaryClass_embedding (familyCoefficientIsometry V) (familyCoefficientIsometry W)
    (blockOperator A C hC hA) (blockOperator_selfAdjoint A C hC hA hs) F G
    (separatedFamilyMultiplier_selfAdjoint o AV (C + 2) hC' hAV r hr hpV hsV)
    (separatedFamilyMultiplier_selfAdjoint o AW (C + 2) hC' hAW r hr hpW hsW)
    (diagonalFamily_square_mem_roe o AV (C + 2) hC' hAV r hr hpV hsV hsqV)
    (diagonalFamily_square_mem_roe o AW (C + 2) hC' hAW r hr hpW hsW hsqW)
    (familyCoefficient_extension V A C hC hA (C + 2) hC' hAV).symm
    (familyCoefficient_extension W A C hC hA (C + 2) hC' hAW).symm
    (finitePropagation_multiplier (separatedMetric_closedBall_finite o) le_rfl
      (familyEmbeddingTransition_propagation V W))

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem localizedSpatialOperator_intertwines (I : E →ₗᵢ[ℂ] H)
    (a : X → E →L[ℂ] E) (b : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (hb : ∀ x, (b x).adjoint = b x)
    (hpa : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hpb : ∑ x, (b x).adjoint.comp (b x) = 1)
    (hI : ∀ x v, b x (I v) = I (a x v))
    (F : E →L[ℂ] E) (G : H →L[ℂ] H) (hF : ∀ v, G (I v) = I (F v)) :
    (localizedSpatialOperator b hpb G).comp (coefficientIsometry I).toContinuousLinearMap =
      (coefficientIsometry I).toContinuousLinearMap.comp (localizedSpatialOperator a hpa F) := by
  ext v x
  change localizedSpatialOperator b hpb G (coefficientIsometry I v) x =
    I (localizedSpatialOperator a hpa F v x)
  rw [localizedSpatialOperator_apply, localizedSpatialOperator_apply]
  simp only [coefficientIsometry_apply, ha, hb]
  have hsum : (∑ y, b y (I (v y))) = I (∑ y, a y (v y)) := by
    simp only [hI, map_sum]
  rw [hsum]
  simp only [sub_apply, one_apply_eq_self, partitionCompression_intertwines I a b ha hb hI F G hF,
    ← map_sub, hI, map_add]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyBoundaryAddition
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity of whole-union coefficient-family boundaries -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]
  {E F G : ℕ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficientFamilyBoundary_add
    (o : ∀ i, Q i) (A : ∀ i, Operator (Q i) (E i)) (B : ∀ i, Operator (Q i) (F i))
    (T : ∀ i, Operator (Q i) (G i))
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D) (hT : ∀ i, ‖T i‖ ≤ K)
    (r : ℝ) (hr : 0 ≤ r)
    (hpA : ∀ i, PropagationLE r (A i)) (hpB : ∀ i, PropagationLE r (B i))
    (hpT : ∀ i, PropagationLE r (T i))
    (hsA : ∀ i, IsSelfAdjoint (A i)) (hsB : ∀ i, IsSelfAdjoint (B i)) (hsT : ∀ i, IsSelfAdjoint (T i))
    (hqA : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (Q i) (E i))))
    (hqB : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (Q i) (F i))))
    (hqT : ∀ i, IsCompactOperator (T i * T i - (1 : Operator (Q i) (G i))))
    (L : ∀ i, E i →ₗᵢ[ℂ] G i) (R : ∀ i, F i →ₗᵢ[ℂ] G i)
    (hLR : ∀ i, (L i).toContinuousLinearMap.adjoint.comp (R i).toContinuousLinearMap = 0)
    (hex : ∀ i, (L i).toContinuousLinearMap.comp (L i).toContinuousLinearMap.adjoint +
      (R i).toContinuousLinearMap.comp (R i).toContinuousLinearMap.adjoint = 1)
    (hL : ∀ i, (T i).comp (coefficientIsometry (L i)).toContinuousLinearMap =
      (coefficientIsometry (L i)).toContinuousLinearMap.comp (A i))
    (hR : ∀ i, (T i).comp (coefficientIsometry (R i)).toContinuousLinearMap =
      (coefficientIsometry (R i)).toContinuousLinearMap.comp (B i))
    (U : ∀ i, G i →ₗᵢ[ℂ] H) :
    letI := separatedMetric o
    coefficientFamilyBoundary o T K hK hT r hr hpT hsT hqT U =
      coefficientFamilyBoundary o A C hC hA r hr hpA hsA hqA (fun i => (U i).comp (L i)) +
      coefficientFamilyBoundary o B D hD hB r hr hpB hsB hqB (fun i => (U i).comp (R i)) := by
  let := separatedMetric o
  let UL := fun i => (U i).comp (L i)
  let UR := fun i => (U i).comp (R i)
  let MT := coefficientFamilyMultiplier o T K hK hT r hr hpT U
  let MA := coefficientFamilyMultiplier o A C hC hA r hr hpA UL
  let MB := coefficientFamilyMultiplier o B D hD hB r hr hpB UR
  have hMTs := coefficientFamilyMultiplier_selfAdjoint o T K hK hT r hr hpT U hsT
  have hMAs := coefficientFamilyMultiplier_selfAdjoint o A C hC hA r hr hpA UL hsA
  have hMBs := coefficientFamilyMultiplier_selfAdjoint o B D hD hB r hr hpB UR hsB
  have hMTd := coefficientFamilyMultiplier_defect o T K hK hT r hr hpT U hsT hqT
  have hMAd := coefficientFamilyMultiplier_defect o A C hC hA r hr hpA UL hsA hqA
  have hMBd := coefficientFamilyMultiplier_defect o B D hD hB r hr hpB UR hsB hqB
  change multiplierBoundaryClass MT hMTs hMTd =
    multiplierBoundaryClass MA hMAs hMAd + multiplierBoundaryClass MB hMBs hMBd
  exact multiplierBoundaryClass_orthogonalEmbeddings
    (familyCoefficientIsometry UL) (familyCoefficientIsometry UR)
    (familyCoefficientIsometry_orthogonal U L R hLR)
    (blockOperator A C hC hA) (blockOperator B D hD hB)
    (blockOperator_selfAdjoint A C hC hA hsA) (blockOperator_selfAdjoint B D hD hB hsB)
    MT MA MB hMTs hMAs hMBs hMTd hMAd hMBd
    (coefficientFamilyMultiplier_value o A C hC hA r hr hpA UL)
    (coefficientFamilyMultiplier_value o B D hD hB r hr hpB UR)
    (coefficientFamilyMultiplier_decomposition_value o A B T C D K hC hD hK hA hB hT
      r hr hpT L R hex hL hR U)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LocalizationUniformEstimate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem partitionCompression_variation_norm_le (a b : X → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ x, (b x).adjoint.comp (b x) = 1)
    (F G : H →L[ℂ] H) (C : ℝ) (hG : ‖G‖ ≤ C) :
    ‖partitionCompression a F - partitionCompression b G‖ ≤
      ‖F - G‖ + 2 * C * ‖partitionMap a - partitionMap b‖ := by
  have hP : ‖partitionMap a‖ ≤ 1 := (partitionIsometry a ha).norm_toContinuousLinearMap_le
  have hQ : ‖partitionMap b‖ ≤ 1 := (partitionIsometry b hb).norm_toContinuousLinearMap_le
  have hPa : ‖(partitionMap a).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hP
  have hQa : ‖(partitionMap b).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hQ
  have h := operatorSandwich_sub_norm_le (partitionMap a).adjoint (partitionMap b).adjoint
    hPa hQa (constantBlock F) (constantBlock G) C ((constantBlock_norm_le G).trans hG)
  have hd : ‖(partitionMap a).adjoint - (partitionMap b).adjoint‖ =
      ‖partitionMap a - partitionMap b‖ := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
  simp only [operatorSandwich, ContinuousLinearMap.adjoint_adjoint, hd,
    constantBlock_sub] at h
  exact h.trans (add_le_add (constantBlock_norm_le (F - G)) le_rfl)

theorem localizedSpatialOperator_variation_norm_le (a b : X → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ x, (b x).adjoint.comp (b x) = 1)
    (F G : H →L[ℂ] H) (C : ℝ) (hG : ‖G‖ ≤ C) :
    ‖localizedSpatialOperator a ha F - localizedSpatialOperator b hb G‖ ≤
      ‖F - G‖ + (4 * C + 2) * ‖partitionMap a - partitionMap b‖ := by
  have hP : ‖partitionMap a‖ ≤ 1 := (partitionIsometry a ha).norm_toContinuousLinearMap_le
  have hQ : ‖partitionMap b‖ ≤ 1 := (partitionIsometry b hb).norm_toContinuousLinearMap_le
  have hK : ‖partitionCompression b G - 1‖ ≤ C + 1 :=
    (norm_sub_le _ _).trans (add_le_add ((partitionCompression_norm_le b hb G).trans hG)
      ContinuousLinearMap.norm_id_le)
  have h := operatorSandwich_sub_norm_le (partitionMap a) (partitionMap b) hP hQ
    (partitionCompression a F - 1) (partitionCompression b G - 1) (C + 1) hK
  have hd : (partitionCompression a F - 1) - (partitionCompression b G - 1) =
      partitionCompression a F - partitionCompression b G := sub_sub_sub_cancel_right _ _ _
  have he : localizedSpatialOperator a ha F - localizedSpatialOperator b hb G =
      operatorSandwich (partitionMap a) (partitionCompression a F - 1) -
        operatorSandwich (partitionMap b) (partitionCompression b G - 1) := by
    simp only [localizedSpatialOperator_eq_sandwich, add_sub_add_left_eq_sub]
  rw [he]
  rw [hd] at h
  have hinner := partitionCompression_variation_norm_le a b ha hb F G C hG
  calc
    _ ≤ ‖partitionCompression a F - partitionCompression b G‖ +
        2 * (C + 1) * ‖partitionMap a - partitionMap b‖ := h
    _ ≤ (‖F - G‖ + 2 * C * ‖partitionMap a - partitionMap b‖) +
        2 * (C + 1) * ‖partitionMap a - partitionMap b‖ := add_le_add hinner le_rfl
    _ = _ := by ring

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedFamilyHomotopy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
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

def sample (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval) : ControlledCycleFamily Q r where
  cycle i := sampledFiniteSum (h.homotopy i) (χ i) (N i) (τ i) h.bound h.one_le_bound
    (fun t => h.norm_le t i)
  unital i := sampledFiniteSum_unital _ _ _ _ _ _ _ (fun t => h.unital t i)
  selfAdjoint i := sampledFiniteSum_selfAdjoint _ _ _ _ _ _ _ (fun t => h.selfAdjoint t i)
  bound := h.bound
  bound_nonneg := zero_le_one.trans h.one_le_bound
  norm_le _ := sampledFiniteSum_norm_le _ _ _ _ _ _ _

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsInclusionNaturality
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-Rips localization respects an actual vertex inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (r : ℝ) (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)

theorem ripsSpatialOperator_inclusion (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) :
    ripsSpatialOperator r (includedCycle r e he c) (includedCycle_unital r e he c hπ) =
      isometricExtension (inclusionIsometry e) (ripsSpatialOperator r c hπ) := by
  exact localizedSpatialOperator_inclusion e (representedSqrt r c)
    (representedSqrt r (includedCycle r e he c)) (representedSqrt_partition r c hπ)
    (representedSqrt_partition r (includedCycle r e he c) (includedCycle_unital r e he c hπ))
    (includedCycle_representedSqrt r e he c)
    (includedCycle_representedSqrt_zero r e he c) c.operator

end CoarseAssembly.Rips

end

end OAI
end


