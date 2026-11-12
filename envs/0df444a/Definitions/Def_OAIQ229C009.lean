-- Prove2me | Definitions.Def_OAIQ229C009
-- name    : OAIQ229C009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:26:29.076889+00:00
-- url     : https://prove2.me/theorems/3153c510-d004-4d90-a5f6-d7d55a1513d9
-- title:
--   Definitions bundle OAIQ229C009 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 28 definitions, 1 instance and 56 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.OddCycle.IsDirectSum.blockHom`, `OAI.CoarseAssembly.Analytic.OddCycle.IsDirectSum.coordinateEquiv`, `OAI.CoarseAssembly.Analytic.OddCycle.IsDirectSum.coordinates`, `OAI.CoarseAssembly.Analytic.OddCycle.IsDirectSum.inclusion`, `OAI.CoarseAssembly.Analytic.OddCycle.IsDirectSum.regularize`, `OAI.CoarseAssembly.Analytic.OddCycle.UnitaryEquivalent.regularize`, `OAI.CoarseAssembly.Analytic.OddCycle.regularize_precomp`, `OAI.CoarseAssembly.Analytic.compactFamilySlice`, `OAI.CoarseAssembly.Analytic.complementBlockOperator`, `OAI.CoarseAssembly.Analytic.complementHilbertSpace`, `OAI.CoarseAssembly.Analytic.complementIsometry`, `OAI.CoarseAssembly.Analytic.complementProjection`, `OAI.CoarseAssembly.Analytic.familyHilbert`, `OAI.CoarseAssembly.Analytic.familyRepresentation`, `OAI.CoarseAssembly.Analytic.negativeProjection`, `OAI.CoarseAssembly.Analytic.rawCycleIndex`, `OAI.CoarseAssembly.Analytic.rawCycleToeplitz`, `OAI.CoarseAssembly.Analytic.reindexRepeated`, `OAI.CoarseAssembly.Analytic.repeatedHilbert`, `OAI.CoarseAssembly.Analytic.repeatedReindexEquiv`, `OAI.CoarseAssembly.Analytic.singleBlock`, `OAI.CoarseAssembly.Analytic.summandComplement`, `OAI.CoarseAssembly.Analytic.tailInsert`, `OAI.CoarseAssembly.Analytic.tailInsertVector`, `OAI.CoarseAssembly.Analytic.truncateBlocks`, `OAI.CoarseAssembly.Analytic.truncatedBlockSum`, `OAI.CoarseAssembly.Analytic.unitaryExtension`, `OAI.CoarseAssembly.boundaryLoopMetric6`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BilateralShift`, `CoarseAssembly_BlockOperators`, `CoarseAssembly_BlockSumDecomposition`, `CoarseAssembly_BoundaryLoopMaps`, `CoarseAssembly_BoundedTransform`, `CoarseAssembly_BoundedTransformNaturality`, `CoarseAssembly_CayleyNaturality`, `CoarseAssembly_CircleSequenceRepresentation`, `CoarseAssembly_CompactBlockSum`, `CoarseAssembly_CompactFamilyHomotopy`, `CoarseAssembly_CountableHilbertSum`, `CoarseAssembly_CycleDirectSumNormalization`, `CoarseAssembly_CycleUnitaryNormalization`, `CoarseAssembly_DirectSumIndex`, `CoarseAssembly_DirectSumIntertwining`, `CoarseAssembly_FiniteCycleDecomposition`, `CoarseAssembly_FiniteCycleSum`, `CoarseAssembly_FiniteLocalization`, `CoarseAssembly_HilbertHeadTail`, `CoarseAssembly_HomogeneousReindex`, `CoarseAssembly_NegativeProjection`, `CoarseAssembly_OrthogonalBlock`, `CoarseAssembly_OrthogonalCoordinates`, `CoarseAssembly_ProjectionBlocks`, `CoarseAssembly_RawCycleIndex`, `CoarseAssembly_RegularizedCycle`, `CoarseAssembly_RegularizedPrecomposition`, `CoarseAssembly_RepresentedIndex`, `CoarseAssembly_ShiftIndex`, `CoarseAssembly_SummandComplement`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C000` and `OAIQ229C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C016`, `OAIQ229C017`, `OAIQ229C018` and `OAIQ229C019`.
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
import Definitions.Def_OAIQ229C000
import Definitions.Def_OAIQ229C001

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform block operators on Hilbert sums

The averaging operators used in the transfer act separately on finite
fibers. A uniform norm bound, rather than finiteness of the set of fibers,
makes their direct sum a bounded operator. The resulting operator admits the uniform approximation needed for the
fiber projection.
-/

noncomputable section

namespace CoarseAssembly

open Filter
open scoped Topology

variable {ι : Type*} {E F : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]

theorem blockOperator_norm_le (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) : ‖blockOperator A C hC hA‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (blockLinear_norm_le A C hC hA)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BilateralShift
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separable Hilbert space and bilateral shift for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

open TopologicalSpace

theorem bilateralShift_unitary : star bilateralShift * bilateralShift = 1 ∧
    bilateralShift * star bilateralShift = 1 := by
  have hs : star bilateralShift = (bilateralShiftEquiv.symm : CircleSequence →L[ℂ] CircleSequence) :=
    bilateralShiftEquiv.adjoint_eq_symm
  rw [hs]
  constructor <;> apply ContinuousLinearMap.ext <;> intro x
  · exact bilateralShiftEquiv.symm_apply_apply x
  · exact bilateralShiftEquiv.apply_symm_apply x

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial block projections

Adjoints commute with uniformly bounded Hilbert direct sums. Under the
explicit flattening equivalence, the sum of constant-fiber projections is
exactly the spatial projection `V V*` used by the Roe transfer.
-/

noncomputable section

namespace CoarseAssembly

open scoped Topology

variable {I : Type*} {E F : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
variable [∀ i, CompleteSpace (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
variable [∀ i, CompleteSpace (F i)]

theorem blockOperator_adjoint (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) :
    (blockOperator A C hC hA).adjoint =
      blockOperator (fun i => (A i).adjoint) C hC
        (fun i => (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _).trans_le (hA i)) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, blockOperator_apply]
  exact tsum_congr (fun i => ContinuousLinearMap.adjoint_inner_left (A i) (y i) (x i))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CountableHilbertSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separable countable sums of the Hilbert spaces in analytic cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

open TopologicalSpace

variable (H : ℕ → HilbertSpace)

/-- Coordinate evaluation is the adjoint of summand inclusion. -/
theorem summandIsometry_adjoint (j : ℕ) :
    (summandIsometry H j).toContinuousLinearMap.adjoint = lp.evalCLM ℂ (fun j => H j) 2 j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun j => H j) j y x

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SummandComplement
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The orthogonal complement of one countable Hilbert summand -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace) (j : ℕ)

def summandComplement : Submodule ℂ (countableHilbertSpace H) :=
  (lp.evalCLM ℂ (fun k => H k) 2 j).ker

instance summandComplement_complete : CompleteSpace (summandComplement H j) :=
  (lp.evalCLM ℂ (fun k => H k) 2 j).isClosed_ker.completeSpace_coe

abbrev complementHilbertSpace : HilbertSpace where
  Carrier := summandComplement H j
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

def complementIsometry : complementHilbertSpace H j →ₗᵢ[ℂ] countableHilbertSpace H :=
  (summandComplement H j).subtypeₗᵢ

def complementProjection : countableHilbertSpace H →L[ℂ] complementHilbertSpace H j :=
  ((1 : End (countableHilbertSpace H)) -
    (summandIsometry H j).toContinuousLinearMap.comp (lp.evalCLM ℂ (fun k => H k) 2 j)).codRestrict
      (summandComplement H j) (by
        intro x
        change (x - lp.single (E := fun k => H k) 2 j (x j)) j = 0
        simp)

theorem complementProjection_coe (x : countableHilbertSpace H) :
    (complementProjection H j x : countableHilbertSpace H) =
      x - summandIsometry H j (x j) := rfl

theorem complementIsometry_adjoint :
    (complementIsometry H j).toContinuousLinearMap.adjoint = complementProjection H j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  symm
  change inner ℂ (x - lp.single (E := fun k => H k) 2 j (x j))
    (y : countableHilbertSpace H) = inner ℂ x (y : countableHilbertSpace H)
  rw [inner_sub_left, lp.inner_single_left]
  have hy : (y : countableHilbertSpace H) j = 0 := y.property
  rw [hy, inner_zero_right, sub_zero]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockSumDecomposition
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a block operator into one summand and its complement -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace) (K : ∀ j, End (H j))
variable (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)

theorem blockOperator_single (j : ℕ) (x : H j) :
    CoarseAssembly.blockOperator K C hC hK (summandIsometry H j x) =
      summandIsometry H j (K j x) := by
  apply lp.ext
  funext k
  change K k (lp.single (E := fun k => H k) 2 j x k) =
    lp.single (E := fun k => H k) 2 j (K j x) k
  by_cases hk : j = k
  · subst k
    simp
  · simp [Pi.single_eq_of_ne (Ne.symm hk)]

def complementBlockOperator (j : ℕ) : End (complementHilbertSpace H j) :=
  (complementIsometry H j).toContinuousLinearMap.adjoint.comp
    ((CoarseAssembly.blockOperator K C hC hK).comp
      (complementIsometry H j).toContinuousLinearMap)

theorem complementBlockOperator_coe (j : ℕ) (x : complementHilbertSpace H j) :
    (complementBlockOperator H K C hC hK j x : countableHilbertSpace H) =
      CoarseAssembly.blockOperator K C hC hK (x : countableHilbertSpace H) := by
  unfold complementBlockOperator
  rw [complementIsometry_adjoint]
  change (complementProjection H j
    (CoarseAssembly.blockOperator K C hC hK (x : countableHilbertSpace H)) :
      countableHilbertSpace H) = _
  rw [complementProjection_coe]
  have hx : (x : countableHilbertSpace H) j = 0 := x.property
  change CoarseAssembly.blockOperator K C hC hK (x : countableHilbertSpace H) -
    summandIsometry H j (K j ((x : countableHilbertSpace H) j)) = _
  rw [hx, map_zero, map_zero, sub_zero]

theorem blockOperator_decomposition (j : ℕ) :
    CoarseAssembly.blockOperator K C hC hK =
      operatorConjugation (summandIsometry H j) (K j) +
        operatorConjugation (complementIsometry H j)
          (complementBlockOperator H K C hC hK j) := by
  apply ContinuousLinearMap.ext
  intro x
  unfold operatorConjugation
  rw [summandIsometry_adjoint, complementIsometry_adjoint]
  change CoarseAssembly.blockOperator K C hC hK x =
    summandIsometry H j (K j (x j)) +
      (complementBlockOperator H K C hC hK j (complementProjection H j x) :
        countableHilbertSpace H)
  rw [complementBlockOperator_coe, complementProjection_coe, map_sub, blockOperator_single]
  abel

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryLoopMaps
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

local instance boundaryLoopMetric6 (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A continuous bounded transform of self-adjoint Fredholm operators

The imaginary part of the Cayley transform is the rational function
`2x / (1 + x²)`. It is contractive and varies continuously even when the
original family has no uniform norm bound.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem boundedTransform_selfAdjoint (F : A) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (boundedTransform F hF) := by
  change star (boundedTransform F hF) = boundedTransform F hF
  simp only [boundedTransform, star_smul, star_sub, star_star, Complex.star_def,
    map_div₀, Complex.conj_I, map_ofNat, neg_div, neg_smul]
  module

theorem boundedTransform_norm_le (F : A) (hF : IsSelfAdjoint F) :
    ‖boundedTransform F hF‖ ≤ 1 := by
  nontriviality A
  unfold boundedTransform
  rw [norm_smul, norm_div, Complex.norm_I, Complex.norm_ofNat]
  have hn := norm_sub_le (cayleyUnitary F hF : A) (star (cayleyUnitary F hF : A))
  rw [norm_star, CStarRing.norm_coe_unitary] at hn
  nlinarith

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the rational boundary formula -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem map_cayleyDenominator (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    Units.map φ.toMonoidHom (cayleyDenominator F hF) =
      cayleyDenominator (φ F) (hF.map φ) := by
  apply Units.ext
  change φ (cayleyDenominator F hF : A) =
    (cayleyDenominator (φ F) (hF.map φ) : B)
  simp only [cayleyDenominator_val, map_add]
  congr 1
  exact φ.commutes Complex.I

theorem map_cayleyUnitary (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    φ (cayleyUnitary F hF : A) = (cayleyUnitary (φ F) (hF.map φ) : B) := by
  have hi := congrArg (fun u : Bˣ => (↑(u⁻¹) : B)) (map_cayleyDenominator φ F hF)
  change φ (↑(cayleyDenominator F hF)⁻¹ : A) =
    (↑(cayleyDenominator (φ F) (hF.map φ))⁻¹ : B) at hi
  simp only [cayleyUnitary_val, map_mul, map_star, hi]
  congr 2
  exact congrArg (fun u : Bˣ => (u : B)) (map_cayleyDenominator φ F hF)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedTransformNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the path-compatible rational normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem map_boundedTransform (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    φ (boundedTransform F hF) = boundedTransform (φ F) (hF.map φ) := by
  simp only [boundedTransform, map_smul, map_sub, map_star, map_cayleyUnitary]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NegativeProjection
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative-frequency projection for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

def negativeProjection : End circleSequenceSpace :=
  CoarseAssembly.blockOperator negativeCoordinate 1 zero_le_one negativeCoordinate_norm

@[simp] theorem negativeProjection_apply (x : CircleSequence) (n : ℤ) :
    negativeProjection x n = if n < 0 then x n else 0 := by
  change (negativeCoordinate n) (x n) = _
  unfold negativeCoordinate
  split_ifs <;> rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleSequenceRepresentation
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous circle functions represented by the bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

theorem bilateralShift_mem_unitary : bilateralShift ∈ unitary (End circleSequenceSpace) :=
  Unitary.mem_iff.mpr bilateralShift_unitary

theorem bilateralShift_spectrum_circle : spectrum ℂ bilateralShift ⊆
    (Submonoid.unitSphere ℂ : Set ℂ) := by
  intro z hz
  exact mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary
    (spectrum_subset_unitary_of_mem_unitary bilateralShift_mem_unitary hz))

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactBlockSum
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact diagonal operators on a countable Hilbert sum -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped Topology

variable (H : ℕ → HilbertSpace) (K : ∀ j, End (H j))

def singleBlock (j : ℕ) : End (countableHilbertSpace H) :=
  (lp.singleContinuousLinearMap ℂ (fun j => H j) 2 j) ∘L K j ∘L
    lp.evalCLM ℂ (fun j => H j) 2 j

theorem singleBlock_compact (j : ℕ) (hK : IsCompactOperator (K j)) :
    IsCompactOperator (singleBlock H K j) :=
  (hK.comp_clm (lp.evalCLM ℂ (fun j => H j) 2 j)).clm_comp
    (lp.singleContinuousLinearMap ℂ (fun j => H j) 2 j)

def truncateBlocks (N j : ℕ) : End (H j) := if j < N then K j else 0

theorem truncateBlocks_norm (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C) :
    ∀ j, ‖truncateBlocks H K N j‖ ≤ C := by
  intro j
  unfold truncateBlocks
  split_ifs
  · exact hK j
  · simpa only [norm_zero] using hC

def truncatedBlockSum (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C) :
    End (countableHilbertSpace H) :=
  CoarseAssembly.blockOperator (truncateBlocks H K N) C hC (truncateBlocks_norm H K N C hC hK)

theorem truncatedBlockSum_apply (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)
    (x : HilbertSum H) (j : ℕ) :
    truncatedBlockSum H K N C hC hK x j = if j < N then K j (x j) else 0 := by
  change (truncateBlocks H K N j) (x j) = _
  unfold truncateBlocks
  split_ifs <;> rfl

theorem truncatedBlockSum_succ (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C) :
    truncatedBlockSum H K (N + 1) C hC hK =
      truncatedBlockSum H K N C hC hK + singleBlock H K N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change truncatedBlockSum H K (N + 1) C hC hK x j =
    truncatedBlockSum H K N C hC hK x j + (lp.single (E := fun j => H j) 2 N (K N (x N))) j
  rw [truncatedBlockSum_apply H K (N + 1) C hC hK x j,
    truncatedBlockSum_apply H K N C hC hK x j]
  by_cases hj : j = N
  · subst j
    simp only [Nat.lt_succ_self, ite_true, if_true, lt_self_iff_false, ite_false, if_false,
      lp.single_apply_self, zero_add]
  · have hlt : j < N + 1 ↔ j < N := by omega
    rw [lp.single_apply_ne (E := fun j => H j) 2 N (K N (x N)) hj, add_zero]
    simp only [hlt]

theorem truncatedBlockSum_compact (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)
    (hc : ∀ j, IsCompactOperator (K j)) (N : ℕ) :
    IsCompactOperator (truncatedBlockSum H K N C hC hK) := by
  induction N with
  | zero =>
    have he : truncatedBlockSum H K 0 C hC hK = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      apply lp.ext
      funext j
      rw [truncatedBlockSum_apply H K 0 C hC hK x j]
      simp
    rw [he]
    exact isCompactOperator_zero
  | succ N ih =>
    rw [truncatedBlockSum_succ]
    exact ih.add (singleBlock_compact H K N (hc N))

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactFamilyHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm continuity of pullback along component-preserving family homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped ZeroAtInfty Topology CStarAlgebra

variable {X Y : ℕ → Type} [∀ j, TopologicalSpace (X j)]
  [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (X j)]
  [∀ j, CompactSpace (Y j)] [∀ j, T2Space (Y j)]

def compactFamilySlice (F : ∀ j, C(Interval × X j, Y j)) (t : Interval) :
    CocompactMap (Sigma X) (Sigma Y) :=
  compactFamilyMap (fun j => (F j).curry t)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularizedCycle
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit norm-one representatives compatible with analytic homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem OddCycle.regularize_unital (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).representation 1 = 1 := c.unitalSelfAdjoint_unital χ

theorem OddCycle.regularize_selfAdjoint (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    IsSelfAdjoint (c.regularize χ).operator := boundedTransform_selfAdjoint _ _

theorem OddCycle.regularize_norm_le (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    ‖(c.regularize χ).operator‖ ≤ 1 := boundedTransform_norm_le _ _

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CycleUnitaryNormalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary equivalence is preserved by explicit cycle normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

theorem unitaryConjugation_eq (U : H ≃ₗᵢ[ℂ] K) (F : End H) :
    U.conjStarAlgEquiv.toStarAlgHom F = operatorConjugation U.toLinearIsometry F := by
  have hadj : U.toLinearIsometry.toContinuousLinearMap.adjoint =
      U.symm.toLinearIsometry.toContinuousLinearMap := U.adjoint_eq_symm
  change U.toLinearIsometry.toContinuousLinearMap.comp
      (F.comp U.symm.toLinearIsometry.toContinuousLinearMap) =
    U.toLinearIsometry.toContinuousLinearMap.comp
      (F.comp U.toLinearIsometry.toContinuousLinearMap.adjoint)
  rw [hadj]

variable {A : Type} [CStarAlgebra A] {c d : OddCycle A}

def OddCycle.UnitaryEquivalent.regularize (e : c.UnitaryEquivalent d) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).UnitaryEquivalent (d.regularize χ) where
  unitary := e.unitary
  representation_eq a := by
    let φ : End c.space →⋆ₐ[ℂ] End d.space := e.unitary.conjStarAlgEquiv.toStarAlgHom
    have hφ (T : End c.space) : φ T = operatorConjugation e.unitary.toLinearIsometry T :=
      unitaryConjugation_eq _ _
    have hr (a : A) : φ (c.representation a) = d.representation a :=
      (hφ _).trans (e.representation_eq a).symm
    change d.representation a + χ a • (1 - d.representation 1) =
      operatorConjugation e.unitary.toLinearIsometry
        (c.representation a + χ a • (1 - c.representation 1))
    rw [← hφ]
    simp only [map_add, map_smul, map_sub, map_one, hr]
  operator_eq := by
    let φ : End c.space →⋆ₐ[ℂ] End d.space := e.unitary.conjStarAlgEquiv.toStarAlgHom
    have hφ (T : End c.space) : φ T = operatorConjugation e.unitary.toLinearIsometry T :=
      unitaryConjugation_eq _ _
    have hr : φ (c.representation 1) = d.representation 1 :=
      (hφ _).trans (e.representation_eq 1).symm
    have hF : φ c.operator = d.operator := (hφ _).trans e.operator_eq.symm
    have hG : (d.unitalSelfAdjoint χ).operator = φ (c.unitalSelfAdjoint χ).operator := by
      rw [d.unitalSelfAdjoint_operator, c.unitalSelfAdjoint_operator, map_symmetricCutDown, hr, hF]
    change boundedTransform (d.unitalSelfAdjoint χ).operator _ =
      operatorConjugation e.unitary.toLinearIsometry
        (boundedTransform (c.unitalSelfAdjoint χ).operator _)
    rw [← hφ]
    erw [map_boundedTransform]
    exact boundedTransform_congr hG _ _

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RepresentedIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Toeplitz index for nonunital representations

A represented unitary is extended by the identity on the complement of the
represented subspace. This supplies a genuine unitary even when the original
representation does not preserve the unit.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def unitaryExtension (c : OddCycle A) (u : A) : End c.space :=
  c.representation u + (1 - c.representation 1)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RawCycleIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Fredholm index defined on every odd cycle

The operator uses the explicit self-adjoint cut-down and varies continuously
along any Fredholm-module homotopy. Its definition makes no spectral choices.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def rawCycleToeplitz (c : OddCycle A) (u : A) : End c.space :=
  toeplitzCompression (H := c.space)
    (positiveProjection (H := c.space)
      (symmetricCutDown (H := c.space) (c.representation 1) c.operator)) (unitaryExtension c u)

def rawCycleIndex (c : OddCycle A) (u : A) : ℤ := (rawCycleToeplitz c u).toLinearMap.index

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OrthogonalCoordinates
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates for an orthogonal direct sum of Fredholm cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

def OddCycle.IsDirectSum.coordinates (h : c.IsDirectSum d e) : e.space →L[ℂ] c.space × d.space :=
  h.left.toContinuousLinearMap.adjoint.prod h.right.toContinuousLinearMap.adjoint

def OddCycle.IsDirectSum.inclusion (h : c.IsDirectSum d e) : c.space × d.space →L[ℂ] e.space :=
  h.left.toContinuousLinearMap.coprod h.right.toContinuousLinearMap

theorem OddCycle.IsDirectSum.orthogonal_reverse (h : c.IsDirectSum d e) :
    h.right.toContinuousLinearMap.adjoint ∘L h.left.toContinuousLinearMap = 0 := by
  have hz := congrArg ContinuousLinearMap.adjoint h.orthogonal
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    map_zero] using hz

theorem OddCycle.IsDirectSum.coordinates_inclusion (h : c.IsDirectSum d e) :
    h.coordinates ∘L h.inclusion = ContinuousLinearMap.id ℂ (c.space × d.space) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · change h.left.toContinuousLinearMap.adjoint (h.left x.1 + h.right x.2) = x.1
    rw [map_add, adjoint_apply_isometry]
    have hz : h.left.toContinuousLinearMap.adjoint (h.right x.2) = 0 :=
      DFunLike.congr_fun h.orthogonal x.2
    rw [hz, add_zero]
  · change h.right.toContinuousLinearMap.adjoint (h.left x.1 + h.right x.2) = x.2
    rw [map_add, adjoint_apply_isometry]
    have hz : h.right.toContinuousLinearMap.adjoint (h.left x.1) = 0 :=
      DFunLike.congr_fun h.orthogonal_reverse x.1
    rw [hz, zero_add]

theorem OddCycle.IsDirectSum.inclusion_coordinates (h : c.IsDirectSum d e) :
    h.inclusion ∘L h.coordinates = ContinuousLinearMap.id ℂ e.space := by
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun h.exhaustive x

def OddCycle.IsDirectSum.coordinateEquiv (h : c.IsDirectSum d e) :
    e.space ≃L[ℂ] c.space × d.space :=
  ContinuousLinearEquiv.equivOfInverse' h.coordinates h.inclusion
    h.coordinates_inclusion h.inclusion_coordinates

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OrthogonalBlock
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The operator algebra of an orthogonal direct sum -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

theorem OddCycle.IsDirectSum.cross_right (h : c.IsDirectSum d e) (T : End c.space) (S : End d.space) :
    operatorConjugation h.right S * operatorConjugation h.left T = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change h.right (S (h.right.toContinuousLinearMap.adjoint
    (h.left (T (h.left.toContinuousLinearMap.adjoint x))))) = 0
  have hz := DFunLike.congr_fun h.orthogonal_reverse (T (h.left.toContinuousLinearMap.adjoint x))
  change h.right.toContinuousLinearMap.adjoint (h.left (T (h.left.toContinuousLinearMap.adjoint x))) = 0 at hz
  rw [hz, map_zero, map_zero]

theorem OddCycle.IsDirectSum.block_mul (h : c.IsDirectSum d e)
    (T T' : End c.space) (S S' : End d.space) :
    h.block T S * h.block T' S' = h.block (T * T') (S * S') := by
  unfold block
  rw [add_mul, mul_add, mul_add, h.cross_left T S', h.cross_right T' S,
    add_zero, zero_add, ← operatorConjugation_mul, ← operatorConjugation_mul]

theorem OddCycle.IsDirectSum.block_add (h : c.IsDirectSum d e)
    (T T' : End c.space) (S S' : End d.space) :
    h.block (T + T') (S + S') = h.block T S + h.block T' S' := by
  change operatorConjugationHom h.left (T + T') + operatorConjugationHom h.right (S + S') = _
  rw [map_add, map_add]
  change (operatorConjugationHom h.left T + operatorConjugationHom h.left T') +
    (operatorConjugationHom h.right S + operatorConjugationHom h.right S') =
    (operatorConjugationHom h.left T + operatorConjugationHom h.right S) +
    (operatorConjugationHom h.left T' + operatorConjugationHom h.right S')
  abel

theorem OddCycle.IsDirectSum.block_smul (h : c.IsDirectSum d e) (z : ℂ)
    (T : End c.space) (S : End d.space) : h.block (z • T) (z • S) = z • h.block T S := by
  change operatorConjugationHom h.left (z • T) + operatorConjugationHom h.right (z • S) = _
  change operatorConjugationHom h.left (z • T) + operatorConjugationHom h.right (z • S) =
    z • (operatorConjugationHom h.left T + operatorConjugationHom h.right S)
  rw [map_smul, map_smul, smul_add]

theorem OddCycle.IsDirectSum.block_one (h : c.IsDirectSum d e) : h.block 1 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun h.exhaustive x

def OddCycle.IsDirectSum.blockHom (h : c.IsDirectSum d e) :
    (End c.space × End d.space) →⋆ₐ[ℂ] End e.space where
  toFun p := h.block p.1 p.2
  map_zero' := by
    change operatorConjugationHom h.left 0 + operatorConjugationHom h.right 0 = 0
    rw [map_zero, map_zero, add_zero]
  map_one' := h.block_one
  map_add' p q := h.block_add p.1 q.1 p.2 q.2
  map_mul' p q := (h.block_mul p.1 q.1 p.2 q.2).symm
  map_star' p := by
    simp only [block, star_add, ← operatorConjugation_star, Prod.fst_star, Prod.snd_star]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change h.block (z • 1) (z • 1) = z • 1
    rw [h.block_smul, h.block_one]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DirectSumIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum additivity of the explicit cycle index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {c d e : OddCycle A}

theorem OddCycle.IsDirectSum.block_cutDown (h : c.IsDirectSum d e)
    (P F : End c.space) (Q G : End d.space) :
    h.block (symmetricCutDown P F) (symmetricCutDown Q G) =
      symmetricCutDown (h.block P Q) (h.block F G) := by
  let φ := h.blockHom
  have hs (r : ℝ) (p : End c.space × End d.space) : φ (r • p) = r • φ p :=
    φ.toAlgHom.map_smul_of_tower r p
  change φ ((1 / 2 : ℝ) • ((P, Q) * (F, G) * (P, Q) +
    star ((P, Q) * (F, G) * (P, Q))) + (1 - (P, Q))) = _
  rw [map_add, hs, map_add, map_star, map_mul, map_mul, map_sub, map_one]
  rfl

theorem OddCycle.IsDirectSum.block_positive (h : c.IsDirectSum d e)
    (F : End c.space) (G : End d.space) :
    h.block (positiveProjection F) (positiveProjection G) =
      positiveProjection (h.block F G) := by
  let φ := h.blockHom
  have hs (r : ℝ) (p : End c.space × End d.space) : φ (r • p) = r • φ p :=
    φ.toAlgHom.map_smul_of_tower r p
  change φ ((1 / 2 : ℝ) • ((F, G) + 1)) = _
  rw [hs, map_add, map_one]
  rfl

theorem OddCycle.IsDirectSum.block_toeplitz (h : c.IsDirectSum d e)
    (P U : End c.space) (Q V : End d.space) :
    h.block (toeplitzCompression P U) (toeplitzCompression Q V) =
      toeplitzCompression (h.block P Q) (h.block U V) := by
  let φ := h.blockHom
  change φ ((P, Q) * (U, V) * (P, Q) + (1 - (P, Q))) = _
  rw [map_add, map_mul, map_mul, map_sub, map_one]
  rfl

theorem OddCycle.IsDirectSum.block_unitaryExtension (h : c.IsDirectSum d e) (u : A) :
    h.block (unitaryExtension c u) (unitaryExtension d u) = unitaryExtension e u := by
  let φ := h.blockHom
  change φ ((c.representation u, d.representation u) +
    (1 - (c.representation 1, d.representation 1))) = _
  rw [map_add, map_sub, map_one]
  change h.block (c.representation u) (d.representation u) +
    (1 - h.block (c.representation 1) (d.representation 1)) = _
  have hr (a : A) : h.block (c.representation a) (d.representation a) = e.representation a :=
    (h.representation_eq a).symm
  rw [hr u, hr 1]
  rfl

theorem OddCycle.IsDirectSum.block_coordinates (h : c.IsDirectSum d e)
    (T : End c.space) (S : End d.space) :
    h.coordinates ∘L h.block T S ∘L h.inclusion = T.prodMap S := by
  have he : h.block T S = h.inclusion ∘L (T.prodMap S) ∘L h.coordinates := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [he]
  simp only [← ContinuousLinearMap.comp_assoc, h.coordinates_inclusion,
    ContinuousLinearMap.id_comp]
  rw [ContinuousLinearMap.comp_assoc, h.coordinates_inclusion,
    ContinuousLinearMap.comp_id]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CycleDirectSumNormalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct sums are preserved by explicit cycle normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem boundedTransform_prod (F : A) (G : B) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    boundedTransform (F, G) (Prod.ext hF.star_eq hG.star_eq) =
      (boundedTransform F hF, boundedTransform G hG) := by
  apply Prod.ext
  · exact map_boundedTransform (StarAlgHom.fst ℂ A B) (F, G) _
  · exact map_boundedTransform (StarAlgHom.snd ℂ A B) (F, G) _

variable {R : Type} [CStarAlgebra R] {c d e : OddCycle R}

theorem OddCycle.IsDirectSum.block_boundedTransform (h : c.IsDirectSum d e)
    (F : End c.space) (G : End d.space) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    h.block (boundedTransform F hF) (boundedTransform G hG) =
      boundedTransform (h.block F G) ((show IsSelfAdjoint (F, G) from Prod.ext hF.star_eq hG.star_eq).map h.blockHom) := by
  have hb := map_boundedTransform h.blockHom (F, G) (Prod.ext hF.star_eq hG.star_eq)
  rw [boundedTransform_prod] at hb
  exact hb

def OddCycle.IsDirectSum.regularize (h : c.IsDirectSum d e) (χ : R →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).IsDirectSum (d.regularize χ) (e.regularize χ) where
  left := h.left
  right := h.right
  orthogonal := h.orthogonal
  exhaustive := h.exhaustive
  representation_eq a := by
    let φ := h.blockHom
    have hr (a : R) : h.block (c.representation a) (d.representation a) = e.representation a :=
      (h.representation_eq a).symm
    change e.representation a + χ a • (1 - e.representation 1) =
      φ ((c.representation a, d.representation a) +
        χ a • (1 - (c.representation 1, d.representation 1)))
    rw [map_add, map_smul, map_sub, map_one φ]
    change e.representation a + χ a • (1 - e.representation 1) =
      h.block (c.representation a) (d.representation a) +
        χ a • (1 - h.block (c.representation 1) (d.representation 1))
    rw [hr a, hr 1]
  operator_eq := by
    have hc := c.unitalSelfAdjoint_selfAdjoint χ
    have hd := d.unitalSelfAdjoint_selfAdjoint χ
    have he := e.unitalSelfAdjoint_selfAdjoint χ
    have hcut : h.block (c.unitalSelfAdjoint χ).operator (d.unitalSelfAdjoint χ).operator =
        (e.unitalSelfAdjoint χ).operator := by
      have hr : h.block (c.representation 1) (d.representation 1) = e.representation 1 :=
        (h.representation_eq 1).symm
      have ho : h.block c.operator d.operator = e.operator := h.operator_eq.symm
      rw [c.unitalSelfAdjoint_operator, d.unitalSelfAdjoint_operator,
        e.unitalSelfAdjoint_operator, h.block_cutDown, hr, ho]
    have hb := h.block_boundedTransform (c.unitalSelfAdjoint χ).operator
      (d.unitalSelfAdjoint χ).operator hc hd
    exact (hb.trans (boundedTransform_congr hcut _ he)).symm

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteLocalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite partition localization of Fredholm cycles

This is the operator step used on each compact Rips component. A represented
square partition of unity localizes the operator without changing its cycle
class. The geometric partition and its propagation control are constructed
separately.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {ι : Type*} [Fintype ι]

@[simp] theorem localizedCycle_operator (c : OddCycle A) (a : ι → A)
    (hF : IsSelfAdjoint c.operator) (ha : ∀ i, IsSelfAdjoint (a i))
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    (localizedCycle c a hF ha hpart).operator = localizedOperator c a := by
  change c.operator + (localizedOperator c a - c.operator) = localizedOperator c a
  abel

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DirectSumIntertwining
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct-sum inclusions intertwine the actual localized operators -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

theorem OddCycle.IsDirectSum.block_apply_left (h : c.IsDirectSum d e)
    (T : End c.space) (S : End d.space) (v : c.space) :
    h.block T S (h.left v) = h.left (T v) := by
  have hz : h.right.toContinuousLinearMap.adjoint (h.left v) = 0 :=
    DFunLike.congr_fun h.orthogonal_reverse v
  change h.left (T (h.left.toContinuousLinearMap.adjoint (h.left v))) +
    h.right (S (h.right.toContinuousLinearMap.adjoint (h.left v))) = _
  rw [adjoint_apply_isometry, hz, map_zero, map_zero, add_zero]

theorem OddCycle.IsDirectSum.block_apply_right (h : c.IsDirectSum d e)
    (T : End c.space) (S : End d.space) (v : d.space) :
    h.block T S (h.right v) = h.right (S v) := by
  have hz : h.left.toContinuousLinearMap.adjoint (h.right v) = 0 :=
    DFunLike.congr_fun h.orthogonal v
  change h.left (T (h.left.toContinuousLinearMap.adjoint (h.right v))) +
    h.right (S (h.right.toContinuousLinearMap.adjoint (h.right v))) = _
  rw [adjoint_apply_isometry, hz, map_zero, map_zero, zero_add]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteCycleSum
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite active sums of analytic cycles

Countably many summands are allowed as an ambient Hilbert space; all but
finitely many cycles are degenerate. The finite active length may later
vary with the component of the coarse disjoint union.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

abbrev familyHilbert (c : ℕ → OddCycle A) (j : ℕ) : HilbertSpace := (c j).space

def familyRepresentation (c : ℕ → OddCycle A) :
    A →⋆ₙₐ[ℂ] End (countableHilbertSpace (familyHilbert c)) where
  toFun a := blockOperator (fun j => (c j).representation a) ‖a‖ (norm_nonneg a)
    (fun j => NonUnitalStarAlgHom.norm_apply_le _ _)
  map_zero' := by
    ext x j
    change (c j).representation 0 (x j) = 0
    rw [map_zero]
    rfl
  map_add' a b := by
    ext x j
    change (c j).representation (a + b) (x j) = _
    rw [map_add]
    rfl
  map_mul' a b := by
    ext x j
    change (c j).representation (a * b) (x j) = _
    rw [map_mul]
    rfl
  map_smul' z a := by
    ext x j
    change (c j).representation (z • a) (x j) = _
    rw [map_smul]
    rfl
  map_star' a := by
    change blockOperator (fun j => (c j).representation (star a)) ‖star a‖ (norm_nonneg _)
        (fun j => NonUnitalStarAlgHom.norm_apply_le _ _) =
      (blockOperator (fun j => (c j).representation a) ‖a‖ (norm_nonneg _)
        (fun j => NonUnitalStarAlgHom.norm_apply_le _ _)).adjoint
    rw [blockOperator_adjoint]
    ext x j
    change (c j).representation (star a) (x j) = ((c j).representation a).adjoint (x j)
    rw [map_star]
    rfl

@[simp] theorem familyRepresentation_apply (c : ℕ → OddCycle A) (a : A)
    (x : countableHilbertSpace (familyHilbert c)) (j : ℕ) :
    familyRepresentation c a x j = (c j).representation a (x j) := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HilbertHeadTail
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The head and tail decomposition used in finite-cycle telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace)

def tailInsertVector (x : countableHilbertSpace (fun j => H (j + 1))) :
    countableHilbertSpace H :=
  ⟨(fun | 0 => 0 | j + 1 => x j), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply (summable_nat_add_iff 1).mp
    exact l2_summable_sq x⟩

theorem tailInsertVector_norm (x : countableHilbertSpace (fun j => H (j + 1))) :
    ‖tailInsertVector H x‖ = ‖x‖ := by
  have he : ‖tailInsertVector H x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq, (l2_summable_sq (tailInsertVector H x)).tsum_eq_zero_add]
    change ‖(0 : H 0)‖ ^ 2 + ∑' j, ‖x j‖ ^ 2 = ∑' j, ‖x j‖ ^ 2
    simp
  nlinarith [norm_nonneg x, norm_nonneg (tailInsertVector H x)]

def tailInsert : countableHilbertSpace (fun j => H (j + 1)) →ₗᵢ[ℂ] countableHilbertSpace H where
  toFun := tailInsertVector H
  map_add' x y := by
    apply lp.ext
    funext j
    cases j with
    | zero => change (0 : H 0) = 0 + 0; simp
    | succ j => rfl
  map_smul' z x := by
    apply lp.ext
    funext j
    cases j <;> simp [tailInsertVector]
  norm_map' := tailInsertVector_norm H

@[simp] theorem tailInsert_zero (x : countableHilbertSpace (fun j => H (j + 1))) :
    tailInsert H x 0 = 0 := rfl

@[simp] theorem tailInsert_succ (x : countableHilbertSpace (fun j => H (j + 1))) (j : ℕ) :
    tailInsert H x (j + 1) = x j := rfl

theorem tailInsert_single (j : ℕ) (y : H (j + 1)) :
    tailInsert H (lp.single 2 j y) = lp.single 2 (j + 1) y := by
  apply lp.ext
  funext k
  cases k with
  | zero => simp [tailInsert, tailInsertVector]
  | succ k =>
    by_cases hk : k = j
    · subst k
      simp [tailInsert, tailInsertVector, lp.single_apply]
    · simp [tailInsert, tailInsertVector, lp.single_apply, hk]

theorem tailInsert_adjoint_apply (x : countableHilbertSpace H) (j : ℕ) :
    (tailInsert H).toContinuousLinearMap.adjoint x j = x (j + 1) := by
  apply ext_inner_left ℂ
  intro y
  rw [← lp.inner_single_left (𝕜 := ℂ) (G := fun j => H (j + 1)),
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (tailInsert H (lp.single 2 j y)) x = inner ℂ y (x (j + 1))
  rw [tailInsert_single, lp.inner_single_left]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteCycleDecomposition
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the first summand off a finite active cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

theorem blockOperator_head_tail (H : ℕ → HilbertSpace) (T : ∀ j, End (H j))
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) :
    blockOperator T C hC hT =
      operatorConjugation (summandIsometry H 0) (T 0) +
        operatorConjugation (tailInsert H)
          (blockOperator (fun j => T (j + 1)) C hC (fun j => hT (j + 1))) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  have hh : (summandIsometry H 0).toContinuousLinearMap.adjoint x = x 0 := by
    rw [summandIsometry_adjoint]
    rfl
  change T j (x j) =
    (lp.single (E := fun j => H j) 2 0 (T 0 ((summandIsometry H 0).toContinuousLinearMap.adjoint x))) j +
      (tailInsert H ((blockOperator (fun j => T (j + 1)) C hC (fun j => hT (j + 1)))
        ((tailInsert H).toContinuousLinearMap.adjoint x))) j
  rw [hh]
  cases j with
  | zero => rw [tailInsert_zero]; simp
  | succ j =>
    rw [tailInsert_succ, blockOperator_apply, tailInsert_adjoint_apply]
    simp

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HomogeneousReindex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing repeated Hilbert summands for finite telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : HilbertSpace)

abbrev repeatedHilbert := countableHilbertSpace (fun _ : ℕ => H)

def reindexRepeated (e : ℕ ≃ ℕ) (x : repeatedHilbert H) : repeatedHilbert H :=
  ⟨fun j => x (e.symm j), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact e.symm.summable_iff.mpr (l2_summable_sq x)⟩

theorem reindexRepeated_norm (e : ℕ ≃ ℕ) (x : repeatedHilbert H) :
    ‖reindexRepeated H e x‖ = ‖x‖ := by
  have he : ‖reindexRepeated H e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.symm.tsum_eq (fun j => ‖x j‖ ^ 2)
  nlinarith [norm_nonneg x, norm_nonneg (reindexRepeated H e x)]

def repeatedReindexEquiv (e : ℕ ≃ ℕ) : repeatedHilbert H ≃ₗᵢ[ℂ] repeatedHilbert H where
  toFun := reindexRepeated H e
  invFun := reindexRepeated H e.symm
  left_inv x := by apply lp.ext; funext j; simp [reindexRepeated]
  right_inv x := by apply lp.ext; funext j; simp [reindexRepeated]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reindexRepeated_norm H e

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularizedPrecomposition
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unital precomposition commutes with continuous regularization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

theorem OddCycle.eq_of_data (c d : OddCycle A) (hs : c.space = d.space)
    (hr : HEq c.representation d.representation) (ho : HEq c.operator d.operator) : c = d := by
  cases c
  cases d
  cases hs
  cases hr
  cases ho
  rfl

theorem conjugation_refl {H : HilbertSpace} (T : End H) :
    operatorConjugation (LinearIsometryEquiv.refl ℂ H).toLinearIsometry T = T := by
  have he : (LinearIsometryEquiv.refl ℂ H).toLinearIsometry.toContinuousLinearMap =
      (1 : End H) := rfl
  unfold operatorConjugation
  rw [he]
  change (ContinuousLinearMap.id ℂ H).comp (T.comp (ContinuousLinearMap.id ℂ H).adjoint) = T
  rw [ContinuousLinearMap.adjoint_id]
  rfl

def OddCycle.regularize_precomp (c : OddCycle A) (φ : B →⋆ₐ[ℂ] A) (χ : A →⋆ₐ[ℂ] ℂ) :
    ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).UnitaryEquivalent
      ((c.regularize χ).precomp φ.toNonUnitalStarAlgHom) where
  unitary := LinearIsometryEquiv.refl ℂ c.space
  representation_eq b := by
    change (c.regularize χ).representation (φ b) =
      operatorConjugation (LinearIsometryEquiv.refl ℂ c.space).toLinearIsometry
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).representation b)
    rw [conjugation_refl]
    change c.representation (φ b) + χ (φ b) • (1 - c.representation 1) =
      c.representation (φ b) + χ (φ b) • (1 - c.representation (φ 1))
    rw [map_one φ]
  operator_eq := by
    change (c.regularize χ).operator =
      operatorConjugation (LinearIsometryEquiv.refl ℂ c.space).toLinearIsometry
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).operator)
    rw [conjugation_refl]
    have hop :
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).unitalSelfAdjoint (χ.comp φ)).operator) =
          (c.unitalSelfAdjoint χ).operator := by
      rw [OddCycle.unitalSelfAdjoint_operator, OddCycle.unitalSelfAdjoint_operator]
      change symmetricCutDown (c.representation (φ 1)) c.operator =
        symmetricCutDown (c.representation 1) c.operator
      rw [map_one φ]
    exact (boundedTransform_congr hop _ _).symm

theorem OddCycle.regularize_precomp_eq (c : OddCycle A) (φ : B →⋆ₐ[ℂ] A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ) =
      (c.regularize χ).precomp φ.toNonUnitalStarAlgHom := by
  refine OddCycle.eq_of_data
    ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ))
    ((c.regularize χ).precomp φ.toNonUnitalStarAlgHom) rfl ?_ ?_
  · apply heq_of_eq
    apply DFunLike.ext
    intro b
    change c.representation (φ b) + χ (φ b) • (1 - c.representation (φ 1)) =
      c.representation (φ b) + χ (φ b) • (1 - c.representation 1)
    rw [map_one φ]
  · apply heq_of_eq
    have h := (c.regularize_precomp φ χ).operator_eq
    change (c.regularize χ).operator =
      operatorConjugation (LinearIsometryEquiv.refl ℂ c.space).toLinearIsometry
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).operator) at h
    rw [conjugation_refl] at h
    exact h.symm

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ShiftIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The index-one compressed bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

theorem bilateralShift_star_apply (x : CircleSequence) (n : ℤ) :
    star bilateralShift x n = x (n + 1) := by
  have hs : star bilateralShift = (bilateralShiftEquiv.symm : CircleSequence →L[ℂ] CircleSequence) :=
    bilateralShiftEquiv.adjoint_eq_symm
  rw [hs]
  rfl

end CoarseAssembly.Analytic

end

end OAI
end


