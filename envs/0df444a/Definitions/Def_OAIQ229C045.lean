-- Prove2me | Definitions.Def_OAIQ229C045
-- name    : OAIQ229C045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T02:34:21.751645+00:00
-- url     : https://prove2.me/theorems/1e4d3538-5f48-4fc6-a93b-2c90f6bfc5e8
-- title:
--   Definitions bundle OAIQ229C045 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 1 definition and 2 theorems. The definitions and types are `OAI.CoarseAssembly.constructedBoundaryAssembly`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_ConstructedBoundaryAssembly`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/ConstructedBoundaryAssembly.lean).
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C043` and `OAIQ229C044` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ229C051`; the proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`.
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
import Definitions.Def_OAIQ229C043
import Definitions.Def_OAIQ229C044

section
-- module Solutions.Q229_CA.CoarseAssembly_ConstructedBoundaryAssembly
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the published assembly interface

The three maps are the constructed analytic cycle index maps. Their two naturality squares follow from spatial inclusion, with
explicit reindexing of the manuscript's vertex sets.
-/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

attribute [local instance] OAI.CoarseAssembly.assembledDiscEq
attribute [local instance] OAI.CoarseAssembly.assemblyBoundaryEq
attribute [local instance] OAI.CoarseAssembly.assemblyFiberEq
attribute [local instance] OAI.CoarseAssembly.assemblyBoundaryComponentMetric
local instance assemblyBoundaryUnionMetric_r12073e_1 : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance assemblyBoundaryMetric_r12073e_1 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.assemblyFiberComponentMetric
local instance assemblyFiberUnionMetric_r12073e_1 : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase
local instance assemblyTotalMetric_r12073e_1 : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit
theorem constructedBoundaryIndex_natural_base (n : ℕ) :
    (constructedBaseIndex.atScale n).comp (pushforward (boundaryBaseCoarsening.atScale n)) =
      (OperatorKTheory.map boundaryBaseRoeHom).comp (constructedBoundaryIndex.atScale n) := by
  apply DFunLike.ext
  intro a
  let b := pushforward (boundaryInverseCoarsening.atScale n) a
  let z := separatedRipsIndex boundaryRoot n (Nat.cast_nonneg n) b
  have h := DFunLike.congr_fun
    (separatedRipsIndex_inclusion boundaryRoot discBoundaryBase (Nat.cast_nonneg n)
      boundaryComponentToBase boundaryComponentToBase_nonexpanding (fun _ => rfl)
      boundaryBaseComponents_nonexpanding) b
  change separatedRipsIndex discBoundaryBase n (Nat.cast_nonneg n)
      (pushforward (boundaryBaseComponentsMap n) b) =
    OperatorKTheory.map boundaryBaseComponentsRoeHom z at h
  have hg := DFunLike.congr_fun (congrArg pushforward (boundaryBaseComponentsMap_eq n)) a
  have hp := DFunLike.congr_fun
    (pushforward_comp (boundaryInverseCoarsening.atScale n) (boundaryBaseComponentsMap n)) a
  have hg' := hp.symm.trans hg
  simp only [constructedBaseIndex, constructedBoundaryIndex, CompatibleIndexFamily.mapTarget,
    CompatibleIndexFamily.transport, separatedIndexFamily_atScale, AddMonoidHom.comp_apply]
  change OperatorKTheory.map baseReindexRoeHom
      (separatedRipsIndex discBoundaryBase n (Nat.cast_nonneg n)
        (pushforward (boundaryBaseCoarsening.atScale n) a)) =
    OperatorKTheory.map boundaryBaseRoeHom (OperatorKTheory.map boundaryReindexRoeHom z)
  have hk := DFunLike.congr_fun
    (congrArg OperatorKTheory.map boundaryBaseComponentsRoeHom_eq) z
  have hi := (congrArg (separatedRipsIndex discBoundaryBase n (Nat.cast_nonneg n)) hg').symm.trans h
  have hkl := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryBaseComponentsRoeHom baseReindexRoeHom) z
  have hkr := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryReindexRoeHom boundaryBaseRoeHom) z
  exact (congrArg (OperatorKTheory.map baseReindexRoeHom) hi).trans
    (hkl.symm.trans (hk.trans hkr))

theorem constructedBoundaryIndex_natural_total (n : ℕ) :
    (constructedTotalIndex.atScale n).comp (pushforward (boundaryTotalCoarsening.atScale n)) =
      (OperatorKTheory.map boundaryTotalRoeHom).comp (constructedBoundaryIndex.atScale n) := by
  apply DFunLike.ext
  intro a
  let b := pushforward (boundaryInverseCoarsening.atScale n) a
  let z := separatedRipsIndex boundaryRoot n (Nat.cast_nonneg n) b
  have h := DFunLike.congr_fun
    (separatedRipsIndex_inclusion boundaryRoot fiberBoundaryBase (Nat.cast_nonneg n)
      boundaryFiberEmbedding boundaryFiberComponent_nonexpanding (fun _ => rfl)
      boundaryFiberComponents_nonexpanding) b
  change separatedRipsIndex fiberBoundaryBase n (Nat.cast_nonneg n)
      (pushforward (boundaryFiberComponentsMap n) b) =
    OperatorKTheory.map boundaryFiberComponentsRoeHom z at h
  have hg := DFunLike.congr_fun (congrArg pushforward (boundaryFiberComponentsMap_eq n)) a
  have hp := DFunLike.congr_fun
    (pushforward_comp (boundaryInverseCoarsening.atScale n) (boundaryFiberComponentsMap n)) a
  have hq := DFunLike.congr_fun
    (pushforward_comp (boundaryTotalCoarsening.atScale n) (totalToFiberCoarsening.atScale n)) a
  have hg' := hp.symm.trans (hg.trans hq)
  simp only [constructedTotalIndex, constructedBoundaryIndex, CompatibleIndexFamily.transport,
    separatedIndexFamily_atScale, AddMonoidHom.comp_apply]
  change OperatorKTheory.map fiberReindexRoeHom
      (separatedRipsIndex fiberBoundaryBase n (Nat.cast_nonneg n)
        (pushforward (totalToFiberCoarsening.atScale n)
          (pushforward (boundaryTotalCoarsening.atScale n) a))) =
    OperatorKTheory.map boundaryTotalRoeHom (OperatorKTheory.map boundaryReindexRoeHom z)
  have hk := DFunLike.congr_fun
    (congrArg OperatorKTheory.map boundaryFiberComponentsRoeHom_eq) z
  have hi := (congrArg (separatedRipsIndex fiberBoundaryBase n (Nat.cast_nonneg n)) hg').symm.trans h
  have hkl := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryFiberComponentsRoeHom fiberReindexRoeHom) z
  have hkr := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryReindexRoeHom boundaryTotalRoeHom) z
  exact (congrArg (OperatorKTheory.map fiberReindexRoeHom) hi).trans
    (hkl.symm.trans (hk.trans hkr))

/-- The published interface is now supplied by the constructed analytic index. -/
def constructedBoundaryAssembly : PublishedBoundaryAssemblyInput where
  boundary := constructedBoundaryIndex
  base := constructedBaseIndex
  total := constructedTotalIndex
  natural_base := constructedBoundaryIndex_natural_base
  natural_total := constructedBoundaryIndex_natural_total

end CoarseAssembly

end

end OAI
end


