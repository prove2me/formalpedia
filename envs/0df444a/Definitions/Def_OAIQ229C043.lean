-- Prove2me | Definitions.Def_OAIQ229C043
-- name    : OAIQ229C043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T23:46:16.117896+00:00
-- url     : https://prove2.me/theorems/dcbc6da7-ef6a-4bf4-b8b9-bd35f13ac23d
-- title:
--   Definitions bundle OAIQ229C043 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 15 definitions and 8 theorems. The definitions and types are `OAI.CoarseAssembly.baseReindexRoeHom`, `OAI.CoarseAssembly.boundaryBaseComponentsMap`, `OAI.CoarseAssembly.boundaryBaseComponentsRoeHom`, `OAI.CoarseAssembly.boundaryFiberComponentsMap`, `OAI.CoarseAssembly.boundaryFiberComponentsRoeHom`, `OAI.CoarseAssembly.boundaryInverseCoarsening`, `OAI.CoarseAssembly.constructedBaseIndex`, `OAI.CoarseAssembly.constructedBoundaryIndex`, `OAI.CoarseAssembly.diagramBaseRoeAdd`, `OAI.CoarseAssembly.diagramBoundaryRoeAdd`, `OAI.CoarseAssembly.diagramBoundaryUnionMetric`, `OAI.CoarseAssembly.diagramFiberRoeAdd`, `OAI.CoarseAssembly.diagramFiberUnionMetric`, `OAI.CoarseAssembly.indexSquareBoundaryUnionMetric`, `OAI.CoarseAssembly.indexSquareFiberUnionMetric`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_ConcreteIndexDiagrams`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ConcreteIndexDiagrams.lean), [`CoarseAssembly_ConcreteIndexFamilies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ConcreteIndexFamilies.lean), [`CoarseAssembly_ConcreteIndexSquares`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ConcreteIndexSquares.lean), [`CoarseAssembly_SeparatedCoarseAssembly`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/SeparatedCoarseAssembly.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundle `OAIQ229C042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C045`, `OAIQ229C047` and `OAIQ229C049`.
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
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Definitions.Def_OAIQ229C042

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedCoarseAssembly
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed coarse assembly for the separated finite-component application

The maps are defined on actual locally finite analytic K-homology and are
compatible with coarsening by the proved finite-tail argument.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

@[simp] theorem separatedIndexFamily_atScale (o : ∀ i, Q i) (n : ℕ) :
    letI := separatedMetric o
    (separatedIndexFamily o).atScale n = separatedRipsIndex o n (Nat.cast_nonneg n) := by
  let := separatedMetric o
  dsimp only [separatedIndexFamily]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    intro r s hrs a
    exact DFunLike.congr_fun (separatedRipsIndex_coarsen o
      (Nat.cast_nonneg r) (Nat.cast_nonneg s) (by exact_mod_cast hrs)) a

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteIndexFamilies
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three constructed analytic index families used by the counterexample -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

attribute [local instance] OAI.CoarseAssembly.constructedFiberComponentEq

attribute [local instance] OAI.CoarseAssembly.constructedFiberComponentMetric

attribute [local instance] OAI.CoarseAssembly.constructedTotalMetric

attribute [local instance] OAI.CoarseAssembly.constructedDiscEq
attribute [local instance] OAI.CoarseAssembly.constructedBoundaryComponentEq
attribute [local instance] OAI.CoarseAssembly.constructedBoundaryComponentMetric
attribute [local instance] OAI.CoarseAssembly.constructedBoundaryMetric
theorem boundaryReindex_isometry :
    letI := separatedMetric boundaryRoot
    Isometry boundaryReindex := by
  let := separatedMetric boundaryRoot
  exact Isometry.of_dist_eq (boundaryReindex_dist elementaryMoves chosenHolonomyUnit)

def boundaryInverseCoarsening : CoarseningMorphism (coarsening BoundaryVertex)
    (letI := separatedMetric boundaryRoot; coarsening (Sigma BoundaryComponent)) := by
  let := separatedMetric boundaryRoot
  exact embeddingCoarsening boundaryReindex.symm.toEmbedding
    (fun x y => ((equiv_inverse_isometry boundaryReindex boundaryReindex_isometry).dist_eq x y).le)

def constructedBoundaryIndex : CompatibleIndexFamily (coarsening BoundaryVertex) BoundaryRoe :=
  (separatedIndexFamily (Q := BoundaryComponent) boundaryRoot).transport boundaryInverseCoarsening boundaryReindexRoeHom

def baseReindexRoeHom :
    (letI := separatedBaseEq; algebra (X := BaseUnion) (H := AmpleSpace)) →⋆ₙₐ[ℂ] BaseRoe :=
  @inclusionHom BaseUnion BaseUnion AmpleSpace separatedBaseEq baseUnionDecidableEq
    _ _ _ _ _ (Function.Embedding.refl BaseUnion) (fun _ _ => le_rfl)

def constructedBaseIndex : CompatibleIndexFamily (coarsening BaseUnion) BaseRoe :=
  (separatedIndexFamily (Q := Disc) discBoundaryBase).mapTarget baseReindexRoeHom

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteIndexDiagrams
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact geometric and Roe squares for the two boundary inclusions -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance concreteDiscEq_rb0913f_1 (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
attribute [local instance] OAI.CoarseAssembly.concreteDiagramBoundaryEq
attribute [local instance] OAI.CoarseAssembly.concreteDiagramFiberEq
attribute [local instance] OAI.CoarseAssembly.concreteDiagramBoundaryComponentMetric
attribute [local instance] OAI.CoarseAssembly.concreteDiagramBoundaryMetric
attribute [local instance] OAI.CoarseAssembly.concreteDiagramFiberComponentMetric
attribute [local instance] OAI.CoarseAssembly.concreteDiagramTotalMetric
local instance diagramBoundaryUnionMetric : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance diagramFiberUnionMetric : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase
local instance diagramBoundaryRoeAdd : AddCommMonoid (algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) := inferInstance
local instance diagramFiberRoeAdd : AddCommMonoid (algebra (X := Sigma FiberVertex) (H := AmpleSpace)) := inferInstance
local instance diagramBaseRoeAdd : AddCommMonoid (letI := separatedBaseEq; algebra (X := BaseUnion) (H := AmpleSpace)) := by
  letI := separatedBaseEq
  infer_instance

theorem boundaryBaseComponents_nonexpanding :
    letI := separatedMetric boundaryRoot
    ∀ x y, dist (componentEmbedding boundaryComponentToBase x)
      (componentEmbedding boundaryComponentToBase y) ≤ dist x y :=
  componentEmbedding_nonexpanding boundaryRoot discBoundaryBase boundaryComponentToBase
    boundaryComponentToBase_nonexpanding (fun _ => rfl)

theorem boundaryFiberComponents_nonexpanding :
    letI := separatedMetric boundaryRoot
    letI := separatedMetric fiberBoundaryBase
    ∀ x y, dist (componentEmbedding boundaryFiberEmbedding x)
      (componentEmbedding boundaryFiberEmbedding y) ≤ dist x y :=
  componentEmbedding_nonexpanding boundaryRoot fiberBoundaryBase boundaryFiberEmbedding
    boundaryFiberComponent_nonexpanding (fun _ => rfl)

def boundaryBaseComponentsRoeHom :
    (letI := separatedMetric boundaryRoot;
      algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) →⋆ₙₐ[ℂ]
    (letI := separatedBaseEq; algebra (X := BaseUnion) (H := AmpleSpace)) := by
  let := separatedMetric boundaryRoot
  exact @inclusionHom (Sigma BoundaryComponent) BaseUnion AmpleSpace _ separatedBaseEq
    _ _ _ _ _ (componentEmbedding boundaryComponentToBase) boundaryBaseComponents_nonexpanding

def boundaryFiberComponentsRoeHom :
    (letI := separatedMetric boundaryRoot;
      algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) →⋆ₙₐ[ℂ]
    (letI := separatedMetric fiberBoundaryBase;
      algebra (X := Sigma FiberVertex) (H := AmpleSpace)) := by
  let := separatedMetric boundaryRoot
  let := separatedMetric fiberBoundaryBase
  exact inclusionHom (X := Sigma BoundaryComponent) (Y := Sigma FiberVertex) (H := AmpleSpace)
    (componentEmbedding boundaryFiberEmbedding) boundaryFiberComponents_nonexpanding

theorem boundaryBaseComponentsRoeHom_eq :
    baseReindexRoeHom.comp boundaryBaseComponentsRoeHom =
      boundaryBaseRoeHom.comp boundaryReindexRoeHom := by
  let := separatedMetric boundaryRoot
  have hf := @inclusionHom_comp (Sigma BoundaryComponent) BaseUnion BaseUnion AmpleSpace
    _ separatedBaseEq baseUnionDecidableEq _ _ _ _ _ _
    (componentEmbedding boundaryComponentToBase) (Function.Embedding.refl BaseUnion)
    boundaryBaseComponents_nonexpanding (fun _ _ => le_rfl)
  have hb := inclusionHom_comp (X := Sigma BoundaryComponent) (Y := BoundaryVertex) (Z := BaseUnion)
    (H := AmpleSpace) boundaryReindex.toEmbedding boundaryToBase
    (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)
  exact hf.trans hb.symm

theorem boundaryFiberComponentsRoeHom_eq :
    fiberReindexRoeHom.comp boundaryFiberComponentsRoeHom =
      boundaryTotalRoeHom.comp boundaryReindexRoeHom := by
  let := separatedMetric boundaryRoot
  let := separatedMetric fiberBoundaryBase
  have hf := inclusionHom_comp (X := Sigma BoundaryComponent) (Y := Sigma FiberVertex)
    (Z := VertexUnion) (H := AmpleSpace)
    (componentEmbedding boundaryFiberEmbedding) totalToFiber.symm.toEmbedding
    boundaryFiberComponents_nonexpanding
    (fun x y => ((equiv_inverse_isometry totalToFiber
      (Isometry.of_dist_eq totalToFiber_dist)).dist_eq x y).le)
  have hb := inclusionHom_comp (X := Sigma BoundaryComponent) (Y := BoundaryVertex)
    (Z := VertexUnion) (H := AmpleSpace) boundaryReindex.toEmbedding boundaryToVertex
    (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
    (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)
  exact hf.trans hb.symm

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteIndexSquares
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Rips-map squares for the constructed index families -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance squareDiscEq_rb0913f_1 (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
local instance indexSquareBoundaryEq_rb0913f_1 (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance indexSquareFiberEq_rb0913f_1 (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
attribute [local instance] OAI.CoarseAssembly.indexSquareBoundaryComponentMetric
local instance indexSquareBoundaryUnionMetric : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance indexSquareBoundaryMetric_rb0913f_1 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.indexSquareFiberComponentMetric
local instance indexSquareFiberUnionMetric : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase

local instance indexSquareTotalMetric_rb0913f_1 : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit
def boundaryBaseComponentsMap (r : ℝ) : CocompactMap (Point (Sigma BoundaryComponent) r) (Point BaseUnion r) :=
  embeddingMap (componentEmbedding boundaryComponentToBase) boundaryBaseComponents_nonexpanding r

def boundaryFiberComponentsMap (r : ℝ) :
    CocompactMap (Point (Sigma BoundaryComponent) r) (Point (Sigma FiberVertex) r) :=
  embeddingMap (componentEmbedding boundaryFiberEmbedding) boundaryFiberComponents_nonexpanding r

theorem boundaryBaseComponentsMap_eq (n : ℕ) :
    (boundaryBaseComponentsMap n).comp (boundaryInverseCoarsening.atScale n) =
      boundaryBaseCoarsening.atScale n := by
  change (embeddingMap _ _ _).comp (embeddingMap _ _ _) = embeddingMap _ _ _
  rw [embeddingMap_comp]
  rfl

theorem boundaryFiberComponentsMap_eq (n : ℕ) :
    (boundaryFiberComponentsMap n).comp (boundaryInverseCoarsening.atScale n) =
      (totalToFiberCoarsening.atScale n).comp (boundaryTotalCoarsening.atScale n) := by
  change (embeddingMap _ _ _).comp (embeddingMap _ _ _) =
    (embeddingMap _ _ _).comp (embeddingMap _ _ _)
  rw [embeddingMap_comp, embeddingMap_comp]
  rfl

end CoarseAssembly

end

end OAI
end


