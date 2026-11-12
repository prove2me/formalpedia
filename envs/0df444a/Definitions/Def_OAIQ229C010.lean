-- Prove2me | Definitions.Def_OAIQ229C010
-- name    : OAIQ229C010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T06:00:25.651194+00:00
-- url     : https://prove2.me/theorems/dd3e75f3-7401-4dd2-8667-e8c9fb3ef151
-- title:
--   Definitions bundle OAIQ229C010 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 160 declarations of OpenAI's Lean: 30 definitions, 1 inductive type or structure and 129 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.characterProjectionRepresentation`, `OAI.CoarseAssembly.Analytic.homotopySlice`, `OAI.CoarseAssembly.Analytic.identityOperatorCycle`, `OAI.CoarseAssembly.Analytic.intervalGrid`, `OAI.CoarseAssembly.Analytic.involutionUnitaryPath`, `OAI.CoarseAssembly.Analytic.lastEndpointFirst`, `OAI.CoarseAssembly.Analytic.partialIsometryDilationPath`, `OAI.CoarseAssembly.Analytic.projectionSignPath`, `OAI.CoarseAssembly.Analytic.quotientProductEquiv`, `OAI.CoarseAssembly.Analytic.restrictComponent`, `OAI.CoarseAssembly.Analytic.rotatePrefix`, `OAI.CoarseAssembly.Analytic.semicircleUnitary`, `OAI.CoarseAssembly.Analytic.semicircleValue`, `OAI.CoarseAssembly.Analytic.sigmaCommutatorBlocks`, `OAI.CoarseAssembly.Analytic.sigmaCycleOperator`, `OAI.CoarseAssembly.Analytic.submoduleProductEquiv`, `OAI.CoarseAssembly.Congruence.childIsometry`, `OAI.CoarseAssembly.Congruence.diagonalHom`, `OAI.CoarseAssembly.Congruence.sameLevelIsometry`, `OAI.CoarseAssembly.ControlledFiberMaps`, `OAI.CoarseAssembly.DiscreteRoe.FiniteHeadReplacement`, `OAI.CoarseAssembly.DiscreteRoe.diagonalMultiplier`, `OAI.CoarseAssembly.DiscreteRoe.rowRestriction`, `OAI.CoarseAssembly.fiberConstant`, `OAI.CoarseAssembly.fiberConstantIsometry`, `OAI.CoarseAssembly.fiberEmbedding`, `OAI.CoarseAssembly.flattenIsometry`, `OAI.CoarseAssembly.quotientCopy`, `OAI.CoarseAssembly.quotientFiberEquiv`, `OAI.CoarseAssembly.reindexFiber`, `OAI.CoarseAssembly.twistedQuotientCopy`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_AlgebraicRoe`, `CoarseAssembly_BlockIsometryRelations`, `CoarseAssembly_BlockOperators`, `CoarseAssembly_CayleyBoundary`, `CoarseAssembly_CayleyContinuity`, `CoarseAssembly_CayleyIntertwining`, `CoarseAssembly_CayleyNormControl`, `CoarseAssembly_CharacterExtension`, `CoarseAssembly_ClopenNaturality`, `CoarseAssembly_ClopenRestriction`, `CoarseAssembly_CoefficientDecomposition`, `CoarseAssembly_CoefficientIsometry`, `CoarseAssembly_CompactHomotopy`, `CoarseAssembly_CompactIndex`, `CoarseAssembly_CongruenceEdgeOperators`, `CoarseAssembly_CongruenceFibers`, `CoarseAssembly_CongruenceQuotients`, `CoarseAssembly_CongruenceSurjective`, `CoarseAssembly_CycleIndex`, `CoarseAssembly_DegenerateCutDown`, `CoarseAssembly_DiagonalBoundaryCoordinates`, `CoarseAssembly_DiagonalMultiplier`, `CoarseAssembly_DiagonalSpatialFamily`, `CoarseAssembly_EssentialToeplitzIndex`, `CoarseAssembly_ExplicitCutDown`, `CoarseAssembly_FiberConstants`, `CoarseAssembly_FiberEmbedding`, `CoarseAssembly_FiberedGraph`, `CoarseAssembly_FiniteFiberMaps`, `CoarseAssembly_FiniteHeadNormalization`, `CoarseAssembly_FiniteLocalization`, `CoarseAssembly_HilbertSum`, `CoarseAssembly_HomogeneousReindex`, `CoarseAssembly_InvolutionUnitaryPath`, `CoarseAssembly_MultiplierBoundaryClass`, `CoarseAssembly_PartialIsometryDilation`, `CoarseAssembly_PartitionCompression`, `CoarseAssembly_PartitionInclusion`, `CoarseAssembly_PartitionIsometry`, `CoarseAssembly_ProductIndex`, `CoarseAssembly_ProjectionBlocks`, `CoarseAssembly_ProjectionUnitaryPath`, `CoarseAssembly_PseudolocalAlgebra`, `CoarseAssembly_Roe`, `CoarseAssembly_RoeCalculus`, `CoarseAssembly_SampledHomotopyDecomposition`, `CoarseAssembly_SigmaCycle`, `CoarseAssembly_SigmaCycleRestriction`, `CoarseAssembly_SigmaFunctionNorms`, `CoarseAssembly_ToeplitzProductIndex`, `CoarseAssembly_TransferCriterion`, `CoarseAssembly_UniformCycleNormalization`, `CoarseAssembly_UniformSubdivision`, `CoarseAssembly_UnitalStructureAlgebra`, `CoarseAssembly_UnitaryIndex`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C000`, `OAIQ229C001` and `OAIQ229C002` of this split; the published statement `Theorems.Thm_FredholmBanach_isOpen_isFredholm_index_locallyConstant`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C016`, `OAIQ229C017`, `OAIQ229C018`, `OAIQ229C019`, `OAIQ229C020` and `OAIQ229C021`.
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
import Definitions.Def_OAIQ229C000
import Definitions.Def_OAIQ229C001
import Definitions.Def_OAIQ229C002
import Theorems.Thm_FredholmBanach_isOpen_isFredholm_index_locallyConstant

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockOperators
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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

@[simp] theorem blockIsometry_apply (V : ∀ i, E i →ₗᵢ[ℂ] F i) (x : lp E 2) (i : ι) :
    blockIsometry V x i = V i (x i) := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Roe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Discrete reduced Roe algebras

Operators act on the actual Hilbert sum `ℓ²(X; H)`. Matrix entries are
continuous linear maps on the coefficient Hilbert space. The Roe algebra is
the norm-closed star algebra generated by finite-propagation operators whose
entries, and adjoint entries, are compact. On a discrete space with finite
metric balls these are the usual locally compact generators.

The coefficient space is a parameter; the ample module used in the paper
is obtained by taking it to be an infinite-dimensional separable Hilbert
space. No compactness is imposed on the averaging projection itself.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped Topology

variable {X Y H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [DecidableEq X] [DecidableEq Y]

variable [CompleteSpace H] [PseudoMetricSpace X]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.operatorScalarTower

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.operatorScalarComm

theorem algebra_isClosed : IsClosed (algebra (X := X) (H := H) : Set (Operator X H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RoeCalculus
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-propagation matrix calculus

The local-compactness step of the finite-fiber transfer states that
sandwiching a locally compact, finite-propagation operator by arbitrary
finite-propagation operators preserves local compactness. The multipliers
themselves are not assumed locally compact.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem insert_adjoint (x : X) : (insert (H := H) x).adjoint = coordinate x := by
  ext v
  apply ext_inner_left ℂ
  intro h
  simp [ContinuousLinearMap.adjoint_inner_right, lp.inner_single_left]

theorem coordinate_adjoint (x : X) : (coordinate (H := H) x).adjoint = insert x := by
  rw [← insert_adjoint, ContinuousLinearMap.adjoint_adjoint]

theorem entry_star (T : Operator X H) (x y : X) :
    entry (star T) x y = star (entry T y x) := by
  simp [entry, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    insert_adjoint, coordinate_adjoint, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace H] in
theorem vector_eq_sum (s : Finset X) (v : Module X H)
    (hv : ∀ x, x ∉ s → v x = 0) :
    v = ∑ x ∈ s, insert x (v x) := by
  apply lp.ext
  funext x
  simp only [lp.coeFn_sum, Finset.sum_apply, insert_apply, lp.coeFn_single]
  rw [Finset.sum_pi_single]
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx, hv x hx]

omit [CompleteSpace H] in
/-- Matrix multiplication is a finite sum whenever the right-hand column
has finite support. This avoids any exchange of infinite sums. -/
theorem entry_mul_of_finite_column (T S : Operator X H) (x y : X) (s : Finset X)
    (hs : ∀ z, z ∉ s → entry S z y = 0) :
    entry (T * S) x y = ∑ z ∈ s, entry T x z * entry S z y := by
  ext h
  have hv : S (insert y h) = ∑ z ∈ s, insert z (entry S z y h) := by
    apply vector_eq_sum
    intro z hz
    have := DFunLike.congr_fun (hs z hz) h
    simpa only [entry_apply, insert_apply, zero_apply] using this
  change coordinate x (T (S (insert y h))) = _
  rw [hv, map_sum, map_sum]
  simp only [sum_apply, mul_apply_eq_comp]
  rfl

variable [PseudoMetricSpace X]

theorem PropagationLE.star {r : ℝ} {T : Operator X H}
    (hT : PropagationLE r T) : PropagationLE r (star T) := by
  intro x y hxy
  rw [entry_star, hT y x (by simpa [dist_comm] using hxy), star_zero]

variable (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)

omit [CompleteSpace H] in
theorem column_support {r : ℝ} {T : Operator X H} (hT : PropagationLE r T) (y : X) :
    ∀ z, z ∉ (finiteBalls y r).toFinset → entry T z y = 0 := by
  intro z hz
  apply hT
  simpa only [Set.Finite.mem_toFinset, Metric.mem_closedBall, not_le] using hz

omit [CompleteSpace H] in
include finiteBalls in
theorem PropagationLE.mul {r s : ℝ} {T S : Operator X H}
    (hT : PropagationLE r T) (hS : PropagationLE s S) :
    PropagationLE (r + s) (T * S) := by
  intro x y hxy
  rw [entry_mul_of_finite_column T S x y (finiteBalls y s).toFinset
    (column_support finiteBalls hS y)]
  apply Finset.sum_eq_zero
  intro z hz
  have hzy : dist z y ≤ s := by
    simpa only [Set.Finite.mem_toFinset, Metric.mem_closedBall] using hz
  have hxz : r < dist x z := by
    have htri := dist_triangle x z y
    linarith
  rw [hT x z hxz, zero_mul]

omit [CompleteSpace H] in
include finiteBalls in
theorem CompactEntries.mul_left {T S : Operator X H} {s : ℝ}
    (hT : CompactEntries T) (hS : PropagationLE s S) : CompactEntries (T * S) := by
  intro x y
  rw [entry_mul_of_finite_column T S x y (finiteBalls y s).toFinset
    (column_support finiteBalls hS y)]
  apply compact_sum
  intro z _
  exact (hT x z).comp_clm (entry S z y)

omit [CompleteSpace H] in
include finiteBalls in
theorem CompactEntries.mul_right {T S : Operator X H} {s : ℝ}
    (hS : CompactEntries S) (hprop : PropagationLE s S) : CompactEntries (T * S) := by
  intro x y
  rw [entry_mul_of_finite_column T S x y (finiteBalls y s).toFinset
    (column_support finiteBalls hprop y)]
  apply compact_sum
  intro z _
  exact (hS z y).clm_comp (entry T x z)

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalMultiplier
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete multiplication representation on a discrete ample module -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped ZeroAtInfty

variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def diagonalMultiplier (f : C₀(X, ℂ)) : Operator X H :=
  blockOperator (fun x => f x • (1 : H →L[ℂ] H)) ‖f‖ (norm_nonneg f)
    (fun x => (scalarBlock_norm_le (f x)).trans (f.toBCF.norm_coe_le_norm x))

@[simp] theorem diagonalMultiplier_apply (f : C₀(X, ℂ)) (v : Module X H) (x : X) :
    diagonalMultiplier f v x = f x • v x := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AlgebraicRoe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The algebra of locally compact finite-propagation operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instContinuousStarOperator

omit [CompleteSpace H] in
theorem PropagationLE.add {T S : Operator X H} {r s : ℝ}
    (hT : PropagationLE r T) (hS : PropagationLE s S) :
    PropagationLE (max r s) (T + S) := by
  intro x y hxy
  rw [entry_add, hT x y (lt_of_le_of_lt (le_max_left _ _) hxy),
    hS x y (lt_of_le_of_lt (le_max_right _ _) hxy), add_zero]

omit [CompleteSpace H] in
theorem PropagationLE.smul {T : Operator X H} {r : ℝ}
    (hT : PropagationLE r T) (z : ℂ) : PropagationLE r (z • T) := by
  intro x y hxy
  rw [entry_smul, hT x y hxy, smul_zero]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CycleIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar-unitary index of normalized odd cycles

This constructs the Fredholm operator and its integer index. Descent to the
cycle quotient and the explicit circle-generator calculation are separate
steps; neither is assumed by these declarations.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

variable {A : Type} [CStarAlgebra A]

theorem fredholmIndex_homotopy (T : Interval → End H) (hT : Continuous T)
    (hf : ∀ t, (T t).IsFredholm) :
    (T start).toLinearMap.index = (T finish).toLinearMap.index := by
  have hc : Continuous (fun t => (T t).toLinearMap.index) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hev : ∀ᶠ t' in nhds t, (T t').toLinearMap.index = (T t).toLinearMap.index :=
      hT.continuousAt.eventually
        (FredholmBanach.isOpen_isFredholm_index_locallyConstant.2 (T t) (hf t))
    exact continuousAt_const.congr (hev.mono fun _ h => h.symm)
  exact IsPreconnected.constant isPreconnected_univ hc.continuousOn
    (Set.mem_univ start) (Set.mem_univ finish)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact perturbation invariance of the Fredholm index

The compactness of both the perturbation and its adjoint keeps the straight
line path unitary modulo compact operators. Local constancy of the Fredholm
index then gives invariance, without a spectral choice of normalization.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem fredholmIndex_compactPerturb (T K : End H)
    (hl : IsCompactOperator (star T * T - 1 : End H))
    (hr : IsCompactOperator (T * star T - 1 : End H))
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End H)) :
    T.toLinearMap.index = (T + K).toLinearMap.index := by
  have hf (t : Interval) : (T + (t : ℝ) • K).IsFredholm := by
    obtain ⟨hl', hr'⟩ := essentialUnitary_compactPerturb T ((t : ℝ) • K) hl hr
      (hK.smul _) (compact_star_real_smul hKs _)
    exact isFredholm_of_compact_essential_unitary _ hl' hr'
  have hh := fredholmIndex_homotopy (fun t : Interval => T + (t : ℝ) • K)
    (continuous_const.add (continuous_subtype_val.smul continuous_const)) hf
  simpa only [start, finish, zero_smul, one_smul, add_zero] using hh

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitCutDown
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit represented-subspace cut-down cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem symmetricCutDown_square_compact (c : OddCycle A) :
    IsCompactOperator ((symmetricCutDown (c.representation 1) c.operator) *
      symmetricCutDown (c.representation 1) c.operator - 1 : End c.space) := by
  have h := cutDown_square_compact c
  change IsCompactOperator ((c.operator + representedCorrection c) *
    (c.operator + representedCorrection c) - 1 : End c.space) at h
  have he : c.operator + representedCorrection c =
      symmetricCutDown (c.representation 1) c.operator := by unfold representedCorrection; abel
  rwa [he] at h

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DegenerateCutDown
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degenerate cycles have zero explicit Toeplitz index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem representedCorrection_annihilates (c : OddCycle A) (hd : c.Degenerate) :
    (∀ a, representedCorrection c * c.representation a = 0) ∧
    (∀ a, c.representation a * representedCorrection c = 0) ∧
    (∀ a, star (representedCorrection c) * c.representation a = 0) := by
  let P := c.representation 1
  let K := representedCorrection c
  have hr : K * P = 0 := by
    change (symmetricCutDown P c.operator - c.operator) * P = 0
    rw [symmetricCutDown_sub_mul P c.operator (representation_unit_selfAdjoint c)
      (representation_unit_sq c), hd.1 1, hd.2.2 1]
    simp
  have hl : P * K = 0 := by
    change P * (symmetricCutDown P c.operator - c.operator) = 0
    rw [mul_symmetricCutDown_sub P c.operator (representation_unit_selfAdjoint c)
      (representation_unit_sq c), hd.1 1, hd.2.2 1]
    simp
  have hs : star K * P = 0 := by
    have he : star K * P = K * P - (star c.operator - c.operator) * P := by
      dsimp only [K, representedCorrection]
      rw [star_sub, (symmetricCutDown_selfAdjoint P c.operator (representation_unit_selfAdjoint c)).star_eq]
      noncomm_ring
    rw [he, hr, hd.2.2 1, sub_self]
  have hp (a : A) : P * c.representation a = c.representation a := by
    change c.representation 1 * c.representation a = c.representation a
    rw [← map_mul, one_mul]
  have hpr (a : A) : c.representation a * P = c.representation a := by
    change c.representation a * c.representation 1 = c.representation a
    rw [← map_mul, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [← hp a, ← mul_assoc, hr, zero_mul]
  · intro a
    rw [← hpr a, mul_assoc, hl, mul_zero]
  · intro a
    rw [← hp a, ← mul_assoc, hs, zero_mul]

theorem cutDown_degenerate (c : OddCycle A) (hd : c.Degenerate) : c.cutDown.Degenerate := by
  obtain ⟨hr, hl, hs⟩ := representedCorrection_annihilates c hd
  let K := representedCorrection c
  change (∀ a, (c.operator + K) * c.representation a - c.representation a * (c.operator + K) = 0) ∧
    (∀ a, ((c.operator + K) * (c.operator + K) - 1) * c.representation a = 0) ∧
    (∀ a, (star (c.operator + K) - (c.operator + K)) * c.representation a = 0)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [add_mul, mul_add, hr a, hl a, add_zero, add_zero, hd.1 a]
  · intro a
    have he : ((c.operator + K) * (c.operator + K) - 1) * c.representation a =
        (c.operator * c.operator - 1) * c.representation a +
        c.operator * (K * c.representation a) +
        K * (c.operator * c.representation a - c.representation a * c.operator) +
        (K * c.representation a) * c.operator + K * (K * c.representation a) := by noncomm_ring
    rw [he, hd.2.1 a, hr a, hd.1 a, mul_zero, mul_zero, zero_mul]
    simp
  · intro a
    have he : (star (c.operator + K) - (c.operator + K)) * c.representation a =
        (star c.operator - c.operator) * c.representation a +
          star K * c.representation a - K * c.representation a := by
      rw [star_add]
      noncomm_ring
    rw [he, hd.2.2 a, hs a, hr a, add_zero, sub_self]

theorem cutDown_degenerate_sq (c : OddCycle A) (hd : c.Degenerate) :
    c.cutDown.operator * c.cutDown.operator = 1 := by
  let d := c.cutDown
  have hd' := cutDown_degenerate c hd
  have hp := hd'.2.1 (1 : A)
  have hQ := cutDown_complement c
  have hq : (d.operator * d.operator - 1) * (1 - d.representation 1) = 0 := by
    calc
      _ = d.operator * (d.operator * (1 - d.representation 1)) - (1 - d.representation 1) := by noncomm_ring
      _ = 0 := by rw [hQ, hQ, sub_self]
  apply sub_eq_zero.mp
  calc
    d.operator * d.operator - 1 = (d.operator * d.operator - 1) * d.representation 1 +
        (d.operator * d.operator - 1) * (1 - d.representation 1) := by noncomm_ring
    _ = 0 := by rw [hp, hq, add_zero]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UnitaryIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary invariance of the explicit cycle index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

theorem operatorConjugation_equiv (e : H ≃ₗᵢ[ℂ] K) (T : End H) :
    operatorConjugation e.toLinearIsometry T = e.conjStarAlgEquiv T := by
  have he : e.toLinearIsometry.toContinuousLinearMap.adjoint =
      (e.symm : K →L[ℂ] H) := e.adjoint_eq_symm
  ext x
  change e (T (e.toLinearIsometry.toContinuousLinearMap.adjoint x)) = e (T (e.symm x))
  rw [he]
  rfl

theorem symmetricCutDown_map (φ : End H →⋆ₐ[ℂ] End K) (P F : End H) :
    φ (symmetricCutDown P F) = symmetricCutDown (φ P) (φ F) := by
  have hs (r : ℝ) (T : End H) : φ (r • T) = r • φ T := φ.toAlgHom.map_smul_of_tower r T
  unfold symmetricCutDown
  rw [map_add, hs, map_add, map_star,
    map_mul, map_mul, map_sub, map_one]

theorem positiveProjection_map (φ : End H →⋆ₐ[ℂ] End K) (F : End H) :
    φ (positiveProjection F) = positiveProjection (φ F) := by
  have hs (r : ℝ) (T : End H) : φ (r • T) = r • φ T := φ.toAlgHom.map_smul_of_tower r T
  unfold positiveProjection
  rw [hs, map_add, map_one]

theorem toeplitzCompression_map (φ : End H →⋆ₐ[ℂ] End K) (P U : End H) :
    φ (toeplitzCompression P U) = toeplitzCompression (φ P) (φ U) := by
  simp only [toeplitzCompression, map_add, map_mul, map_sub, map_one]

theorem fredholmIndex_conjugation (e : H ≃ₗᵢ[ℂ] K) (T : End H) (hT : T.IsFredholm) :
    (e.conjStarAlgEquiv T).toLinearMap.index = T.toLinearMap.index := by
  have he := e.toContinuousLinearEquiv.isFredholm
  have hei := e.symm.toContinuousLinearEquiv.isFredholm
  have hz : (e.toContinuousLinearEquiv : H →L[ℂ] K).toLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.bijective
  have hzi : (e.symm.toContinuousLinearEquiv : K →L[ℂ] H).toLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.symm.bijective
  change ((e.toContinuousLinearEquiv : H →L[ℂ] K) ∘L T ∘L
    (e.symm.toContinuousLinearEquiv : K →L[ℂ] H)).toLinearMap.index = _
  rw [he.index_comp (hT.comp hei), hT.index_comp hei, hz, hzi, zero_add, add_zero]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProductIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity of the Fredholm index on products -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

def submoduleProductEquiv (P : Submodule ℂ H) (Q : Submodule ℂ K) :
    P.prod Q ≃ₗ[ℂ] P × Q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1, x.2), x.1.property, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def quotientProductEquiv (P : Submodule ℂ H) (Q : Submodule ℂ K) :
    ((H × K) ⧸ P.prod Q) ≃ₗ[ℂ] (H ⧸ P) × (K ⧸ Q) := by
  let f := P.mkQ.prodMap Q.mkQ
  have hf : Function.Surjective f := by
    rintro ⟨x, y⟩
    obtain ⟨x', rfl⟩ := P.mkQ_surjective x
    obtain ⟨y', rfl⟩ := Q.mkQ_surjective y
    exact ⟨(x', y'), rfl⟩
  have hk : f.ker = P.prod Q := by simp only [f, LinearMap.ker_prodMap, Submodule.ker_mkQ]
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

theorem finrank_submoduleProduct (P : Submodule ℂ H) (Q : Submodule ℂ K)
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q] :
    Module.finrank ℂ (P.prod Q) = Module.finrank ℂ P + Module.finrank ℂ Q := by
  rw [(submoduleProductEquiv P Q).finrank_eq, Module.finrank_prod]

theorem finrank_quotientProduct (P : Submodule ℂ H) (Q : Submodule ℂ K)
    [FiniteDimensional ℂ (H ⧸ P)] [FiniteDimensional ℂ (K ⧸ Q)] :
    Module.finrank ℂ ((H × K) ⧸ P.prod Q) =
      Module.finrank ℂ (H ⧸ P) + Module.finrank ℂ (K ⧸ Q) := by
  rw [(quotientProductEquiv P Q).finrank_eq, Module.finrank_prod]

theorem fredholmIndex_prodMap (T : End H) (S : End K) (hT : T.IsFredholm) (hS : S.IsFredholm) :
    (T.toLinearMap.prodMap S.toLinearMap).index = T.toLinearMap.index + S.toLinearMap.index := by
  let := hT.finite_ker
  let := hS.finite_ker
  let := hT.finite_coker
  let := hS.finite_coker
  have hk : (T.toLinearMap.prodMap S.toLinearMap).ker = T.ker.prod S.ker :=
    LinearMap.ker_prodMap T.toLinearMap S.toLinearMap
  have hr : (T.toLinearMap.prodMap S.toLinearMap).range = T.range.prod S.range :=
    LinearMap.range_prodMap T.toLinearMap S.toLinearMap
  have hkdim : Module.finrank ℂ (T.toLinearMap.prodMap S.toLinearMap).ker =
      Module.finrank ℂ T.ker + Module.finrank ℂ S.ker := by
    rw [hk]
    exact finrank_submoduleProduct T.ker S.ker
  have hrdim : Module.finrank ℂ ((H × K) ⧸ (T.toLinearMap.prodMap S.toLinearMap).range) =
      Module.finrank ℂ (H ⧸ T.range) + Module.finrank ℂ (K ⧸ S.range) := by
    rw [hr]
    exact finrank_quotientProduct T.range S.range
  simp only [LinearMap.index_eq_finrank_sub]
  rw [hkdim, hrdim, Nat.cast_add, Nat.cast_add]
  omega

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberConstants
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized constant subspace of a finite fiber

The fiber embedding sends `h` to the constant vector `|Q|⁻¹ᐟ² h`.
It is an actual linear isometry, including for singleton boundary fibers.
-/

noncomputable section

namespace CoarseAssembly

variable (Q : Type*) [Fintype Q]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem fiberNormalization_nonneg : 0 ≤ fiberNormalization Q := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem fiberNormalization_sq [Nonempty Q] :
    (Fintype.card Q : ℝ) * fiberNormalization Q ^ 2 = 1 := by
  have hn : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  unfold fiberNormalization
  rw [inv_pow, Real.sq_sqrt hn.le]
  exact mul_inv_cancel₀ (ne_of_gt hn)

def fiberConstant (h : H) : lp (fun _ : Q => H) 2 :=
  ⟨fun _ => (fiberNormalization Q : ℂ) • h, Memℓp.all _⟩

@[simp] theorem fiberConstant_apply (h : H) (q : Q) :
    fiberConstant Q h q = (fiberNormalization Q : ℂ) • h := rfl

theorem fiberConstant_norm [Nonempty Q] (h : H) : ‖fiberConstant Q h‖ = ‖h‖ := by
  have hs := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (fiberConstant Q h)
  have hs' : ‖fiberConstant Q h‖ ^ 2 =
      (Fintype.card Q : ℝ) * (fiberNormalization Q * ‖h‖) ^ 2 := by
    simpa [Real.rpow_two, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fiberNormalization_nonneg Q), tsum_fintype] using hs
  have hn := fiberNormalization_sq Q
  have heq : ‖fiberConstant Q h‖ ^ 2 = ‖h‖ ^ 2 := by
    rw [mul_pow, ← mul_assoc, hn, one_mul] at hs'
    exact hs'
  nlinarith [norm_nonneg (fiberConstant Q h), norm_nonneg h]

def fiberConstantIsometry [Nonempty Q] : H →ₗᵢ[ℂ] lp (fun _ : Q => H) 2 where
  toFun := fiberConstant Q
  map_add' x y := by
    apply lp.ext
    funext q
    exact smul_add (fiberNormalization Q : ℂ) x y
  map_smul' a x := by
    apply lp.ext
    funext q
    exact smul_comm (fiberNormalization Q : ℂ) a x
  norm_map' := fiberConstant_norm Q

/-- Singleton boundary fibers have normalization one. -/
@[simp] theorem fiberNormalization_of_unique [Unique Q] : fiberNormalization Q = 1 := by
  simp [fiberNormalization]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HilbertSum
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the Hilbert sum of the finite fibers

The transfer is naturally constructed as a block operator. Flattening its
Hilbert sum identifies it isometrically with the ordinary Roe module on
the sigma type of vertices. Both directions and the norm identity are
constructed from summability of squared norms.
-/

noncomputable section

namespace CoarseAssembly

variable {ι : Type*} {Q : ι → Type*} {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
theorem flattenVector_norm (x : lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    ‖flattenVector x‖ = ‖x‖ := by
  have hsq : ‖flattenVector x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      _ = ∑' q, ‖flattenVector x q‖ ^ 2 := l2_norm_sq _
      _ = ∑' i, ∑' q : Q i, ‖flattenVector x ⟨i, q⟩‖ ^ 2 :=
        Summable.tsum_sigma' (fun i => l2_summable_sq (x i))
          (l2_summable_sq (flattenVector x))
      _ = ∑' i, ‖x i‖ ^ 2 := tsum_congr (fun i => (l2_norm_sq (x i)).symm)
      _ = ‖x‖ ^ 2 := (l2_norm_sq x).symm
  nlinarith [norm_nonneg (flattenVector x), norm_nonneg x]

def flattenIsometry :
    lp (fun i => lp (fun _ : Q i => H) 2) 2 →ₗᵢ[ℂ] lp (fun _ : Sigma Q => H) 2 where
  toFun := flattenVector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := flattenVector_norm

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constant-fiber spatial isometry

This is the actual map from the base Roe module to the fibered Roe module.
On singleton boundary fibers it is exactly the coordinate inclusion.
-/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} (Q : I → Type*) [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fiberEmbedding : lp (fun _ : I => H) 2 →ₗᵢ[ℂ] lp (fun _ : Sigma Q => H) 2 :=
  flattenIsometry.comp (blockIsometry (fun i => fiberConstantIsometry (Q i)))

omit [CompleteSpace H] in
@[simp] theorem fiberEmbedding_apply (x : lp (fun _ : I => H) 2) (i : I) (q : Q i) :
    fiberEmbedding Q x ⟨i, q⟩ = (fiberNormalization (Q i) : ℂ) • x i := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionIsometry
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalMultiplier_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Hilbert-space isometry of a finite square partition -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp] theorem coordinate_partitionMap (a : X → H →L[ℂ] H) (x : X) :
    (coordinate x).comp (partitionMap a) = a x := by
  ext v
  simp [partitionMap, ContinuousLinearMap.comp_apply, coordinate_apply, insert_apply,
    lp.single_apply]

@[simp] theorem partitionIsometry_toContinuousLinearMap (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) :
    (partitionIsometry a hpart).toContinuousLinearMap = partitionMap a := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionCompression
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalMultiplier_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The contraction estimate for finite partition localization -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [DecidableEq X] [CompleteSpace H] in
@[simp] theorem constantBlock_apply (F : H →L[ℂ] H) (v : Module X H) (x : X) :
    constantBlock F v x = F (v x) := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PseudolocalAlgebra
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pseudolocal operators and the controlled structure algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped ZeroAtInfty CStarAlgebra

variable {X H : Type*} [DecidableEq X] [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instIsScalarTowerComplexOperator_2 : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance instSMulCommClassComplexOperator_2 : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UnitalStructureAlgebra
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unit of the controlled pseudolocal algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance instIsScalarTowerComplexOperator_3_r9e3bfe_1 : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance instSMulCommClassComplexOperator_3_r9e3bfe_1 : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
omit [CompleteSpace H] in
theorem propagationLE_one : PropagationLE 0 (1 : Operator X H) := by
  intro x y hxy
  have hne : x ≠ y := by intro h; simp [h] at hxy
  ext v
  simp [entry_apply, lp.single_apply, hne]

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartitionInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite partition localization under vertex inclusions -/

noncomputable section

namespace CoarseAssembly

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

namespace DiscreteRoe

variable {X Y H : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype Y] [DecidableEq Y] [CompleteSpace H] in
@[simp] theorem partitionMap_apply (a : X → H →L[ℂ] H) (v : H) (x : X) :
    partitionMap a v x = a x v := DFunLike.congr_fun (coordinate_partitionMap a x) v

end DiscreteRoe
end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceQuotients
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual congruence quotients and diagonal holonomies

The congruence quotient is `SL₃(ℤ/2^kℤ)`, including the singleton quotient
for `k = 0`.
Its diagonal matrices have entries `t,t⁻¹,1`, and the finite-level matrices
are obtained by the genuine 2-adic reduction maps.
-/

namespace CoarseAssembly.Congruence

theorem diagonal_one {R : Type*} [CommRing R] :
    diagonal (1 : Rˣ) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.diagonal]

/-- The diagonal assignment respects the unit-group multiplication. -/
def diagonalHom {R : Type*} [CommRing R] : Rˣ →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun := diagonal
  map_one' := diagonal_one
  map_mul' := diagonal_mul

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteFiberMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permutations and normalized quotient-copying maps

These are the two types of edge operator in the graph construction:
permutations at equal depth, and normalized copying along a surjective
finite-group quotient. Their norm and constant-vector properties are
proved on the actual finite-fiber Hilbert spaces.
-/

noncomputable section

namespace CoarseAssembly

variable {Q R H : Type*} [Fintype Q] [Fintype R]
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
theorem reindexFiber_norm (e : Q ≃ R) (x : lp (fun _ : Q => H) 2) :
    ‖reindexFiberVector e x‖ = ‖x‖ := by
  have hsq : ‖reindexFiberVector e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq, tsum_fintype, tsum_fintype]
    exact Equiv.sum_comp e.symm (fun q => ‖x q‖ ^ 2)
  nlinarith [norm_nonneg (reindexFiberVector e x), norm_nonneg x]

def reindexFiber (e : Q ≃ R) : lp (fun _ : Q => H) 2 ≃ₗᵢ[ℂ] lp (fun _ : R => H) 2 where
  toFun := reindexFiberVector e
  invFun := reindexFiberVector e.symm
  left_inv x := by apply lp.ext; funext q; simp [reindexFiberVector]
  right_inv x := by apply lp.ext; funext r; simp [reindexFiberVector]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reindexFiber_norm e

@[simp] theorem reindexFiber_apply (e : Q ≃ R) (x : lp (fun _ : Q => H) 2) (r : R) :
    reindexFiber e x r = x (e.symm r) := rfl

theorem reindexFiber_constant (e : Q ≃ R) (h : H) :
    reindexFiber e (fiberConstant Q h) = fiberConstant R h := by
  apply lp.ext
  funext r
  simp only [reindexFiber_apply, fiberConstant_apply, fiberNormalization, Fintype.card_congr e]

section GroupQuotient

variable {G K : Type*} [Group G] [Group K] [Fintype G] [Fintype K]

omit [Fintype G] [Fintype K] in
@[simp] theorem quotientSection_spec (f : G →* K) (hf : Function.Surjective f) (k : K) :
    f (quotientSection f hf k) = k := (hf k).choose_spec

def quotientFiberEquiv (f : G →* K) (hf : Function.Surjective f) : G ≃ ((_k : K) × f.ker) where
  toFun g := ⟨f g, ⟨(quotientSection f hf (f g))⁻¹ * g, by simp⟩⟩
  invFun z := quotientSection f hf z.1 * z.2.val
  left_inv g := by simp
  right_inv z := by
    rcases z with ⟨k, z, hz⟩
    have hz' : f z = 1 := hz
    simp only [map_mul, quotientSection_spec, hz', mul_one]
    congr 1
    apply Subtype.ext
    simp

def quotientCopy (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f) :
    lp (fun _ : K => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 := by
  classical
  exact (reindexFiber (quotientFiberEquiv f hf).symm).toLinearIsometry.comp
    (fiberEmbedding (fun _ : K => f.ker))

@[simp] theorem quotientCopy_apply (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f)
    (x : lp (fun _ : K => ℂ) 2) (g : G) :
    quotientCopy f hf x g = (fiberNormalization f.ker : ℂ) * x (f g) := rfl

theorem quotientCopy_constant (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f) :
    quotientCopy f hf (fiberConstant K (1 : ℂ)) = fiberConstant G 1 := by
  classical
  have hcard : Fintype.card G = Fintype.card K * Fintype.card f.ker := by
    simpa using Fintype.card_congr (quotientFiberEquiv f hf)
  have hnorm : fiberNormalization f.ker * fiberNormalization K = fiberNormalization G := by
    simp only [fiberNormalization, hcard, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg (Fintype.card K)), mul_inv_rev]
  apply lp.ext
  funext g
  simp only [quotientCopy_apply, fiberConstant_apply, smul_eq_mul, mul_one]
  exact_mod_cast hnorm

/-- The shallow-to-deep edge operator, including its right holonomy twist. -/
def twistedQuotientCopy (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f) (a : K) :
    lp (fun _ : K => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 :=
  (quotientCopy f hf).comp (reindexFiber (Equiv.mulRight a)).toLinearIsometry

theorem twistedQuotientCopy_constant (f : G →* K) [Fintype f.ker]
    (hf : Function.Surjective f) (a : K) :
    twistedQuotientCopy f hf a (fiberConstant K (1 : ℂ)) = fiberConstant G 1 := by
  change quotientCopy f hf (reindexFiber (Equiv.mulRight a) (fiberConstant K 1)) = _
  rw [reindexFiber_constant, quotientCopy_constant]

theorem twistedQuotientCopy_apply (f : G →* K) [Fintype f.ker]
    (hf : Function.Surjective f) (a : K) (x : lp (fun _ : K => ℂ) 2) (g : G) :
    twistedQuotientCopy f hf a x g = (fiberNormalization f.ker : ℂ) * x (f g * a⁻¹) := rfl

end GroupQuotient

end CoarseAssembly

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

omit [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (F i)] in
theorem blockIsometry_toCLM (V : ∀ i, E i →ₗᵢ[ℂ] F i) :
    (blockIsometry V).toContinuousLinearMap =
      blockOperator (fun i => (V i).toContinuousLinearMap) 1 zero_le_one
        (fun i => (V i).norm_toContinuousLinearMap_le) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CoefficientIsometry
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric changes of the coefficient Hilbert space

Changing coefficients by a pointwise isometry preserves propagation.
Extending by the identity on its orthogonal complement preserves compact
square defects, as required to place localized cycles on an ample module.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq X] [CompleteSpace E] [CompleteSpace H] in
@[simp] theorem coefficientIsometry_apply (V : E →ₗᵢ[ℂ] H) (v : Module X E) (x : X) :
    coefficientIsometry V v x = V (v x) := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteLocalization
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
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

theorem localizedOperator_sub_eq (c : OddCycle A) (a : ι → A)
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    localizedOperator c a - c.operator =
      ∑ i, c.representation (a i) *
        (c.operator * c.representation (a i) - c.representation (a i) * c.operator) := by
  calc
    localizedOperator c a - c.operator = localizedOperator c a -
        (∑ i, c.representation (a i) * c.representation (a i)) * c.operator := by
      rw [hpart, one_mul]
    _ = ∑ i, (c.representation (a i) * c.operator * c.representation (a i) -
        (c.representation (a i) * c.representation (a i)) * c.operator) := by
      rw [localizedOperator, Finset.sum_mul, ← Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalSpatialFamily
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalMultiplier_apply _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform diagonal families on the actual separated vertex union -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
@[simp] theorem diagonalFamily_apply (A : ∀ i, Operator (V i) H) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (v : Module (Sigma V) H) (i : ℕ) (x : V i) :
    diagonalFamily A C hC hA v ⟨i, x⟩ = A i (rowVector v i) x := rfl

omit [CompleteSpace H] in
@[simp] theorem entry_diagonalFamily_same (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (i : ℕ) (x y : V i) :
    entry (diagonalFamily A C hC hA) ⟨i, x⟩ ⟨i, y⟩ = entry (A i) x y := by
  ext v
  simp only [entry_apply, diagonalFamily_apply, rowVector_single_same]

omit [CompleteSpace H] in
theorem entry_diagonalFamily_ne (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) {i j : ℕ} (hij : i ≠ j)
    (x : V i) (y : V j) :
    entry (diagonalFamily A C hC hA) ⟨i, x⟩ ⟨j, y⟩ = 0 := by
  ext v
  simp only [entry_apply, diagonalFamily_apply, rowVector_single_ne hij, map_zero,
    lp.coeFn_zero, Pi.zero_apply, zero_apply]

variable [∀ i, MetricSpace (V i)] (o : ∀ i, V i)


omit [CompleteSpace H] in
theorem diagonalFamily_propagation (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (r : ℝ)
    (hp : ∀ i, PropagationLE r (A i)) :
    letI := separatedMetric o
    PropagationLE r (diagonalFamily A C hC hA) := by
  let := separatedMetric o
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  by_cases hij : i = j
  · subst j
    rw [entry_diagonalFamily_same]
    apply hp i x y
    simpa only [show dist (⟨i, x⟩ : Sigma V) ⟨i, y⟩ = dist x y from
      separatedDist_same o i x y] using hxy
  · exact entry_diagonalFamily_ne A C hC hA hij x y

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyBoundary
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rational representative of the odd analytic boundary

For a self-adjoint `F`, the square of its Cayley transform, with a minus sign,
equals one modulo the square defect `F² - 1`. This construction will be applied
to the Roe ideal in the controlled pseudolocal algebra.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem rationalBoundaryUnitary_defect (F : A) (hF : IsSelfAdjoint F) :
    ((rationalBoundaryUnitary F hF : A) - 1) *
        (cayleyDenominator F hF : A) ^ 2 = -2 * (F ^ 2 - 1) := by
  let b := cayleyDenominator F hF
  have hc : Commute (star (b : A)) (b : A) := cayleyDenominator_normal F hF
  have hci : Commute (star (b : A)) (↑b⁻¹ : A) := hc.units_inv_right
  have he : (cayleyUnitary F hF : A) ^ 2 * (b : A) ^ 2 = star (b : A) ^ 2 := by
    rw [cayleyUnitary_val, hci.mul_pow, mul_assoc,
      ← (Commute.refl (b : A)).units_inv_left.mul_pow, Units.inv_mul, one_pow, mul_one]
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul]
  rw [← pow_two]
  rw [sub_mul, neg_mul, he, one_mul]
  rw [cayleyDenominator_star, cayleyDenominator_val]
  have hI : (algebraMap ℂ A Complex.I) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hcI := Algebra.commutes (R := ℂ) (A := A) Complex.I F
  have hI' : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I = -1 := by
    simpa only [pow_two] using hI
  noncomm_ring [hcI, hI']
  norm_num

theorem rationalBoundaryUnitary_sub_one_mem (I : TwoSidedIdeal A)
    (F : A) (hF : IsSelfAdjoint F) (hdefect : F ^ 2 - 1 ∈ I) :
    (rationalBoundaryUnitary F hF : A) - 1 ∈ I := by
  let b := cayleyDenominator F hF
  have h : ((rationalBoundaryUnitary F hF : A) - 1) * (b : A) ^ 2 ∈ I := by
    rw [rationalBoundaryUnitary_defect]
    exact I.mul_mem_left _ _ hdefect
  have h' := I.mul_mem_right _ ((↑b⁻¹ : A) ^ 2) h
  have hc : Commute (b : A) (↑b⁻¹ : A) := (Commute.refl (b : A)).units_inv_right
  simpa only [mul_assoc, ← hc.mul_pow, Units.mul_inv, one_pow, mul_one] using h'

theorem rationalBoundaryUnitary_eq_one (F : A) (hF : IsSelfAdjoint F)
    (hsq : F ^ 2 = 1) : rationalBoundaryUnitary F hF = 1 := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  have h := rationalBoundaryUnitary_defect F hF
  rw [hsq, sub_self, mul_zero] at h
  apply (Units.mul_left_inj (cayleyDenominator F hF ^ 2)).mp
  simpa only [Units.val_pow_eq_pow_val, zero_mul, Submonoid.coe_one] using h

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplierBoundaryClass
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.diagonalFamily_apply _root_.OAI.CoarseAssembly.DiscreteRoe.entry_diagonalFamily_same _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary classes in the closed Roe multiplier algebra

A controlled Rips operator is a Roe multiplier even when it is not
pseudolocal for the discrete vertex representation. The ideal-boundary
construction is therefore performed in this actual closed multiplier
algebra before constructing the coarse assembly map.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem mem_multiplierRoeIdeal (T : multiplierAlgebra (X := X) (H := H)) :
    T ∈ multiplierRoeIdeal (X := X) (H := H) ↔ T.val ∈ algebra (X := X) (H := H) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionUnitaryPath
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit unitary path for changing a projection's sign -/

noncomputable section

namespace CoarseAssembly.Analytic

def semicircleValue (t : Interval) : ℂ :=
  ⟨1 - 2 * t.val, 2 * Real.sqrt (t.val * (1 - t.val))⟩

theorem semicircleValue_star_mul (t : Interval) :
    star (semicircleValue t) * semicircleValue t = 1 := by
  have hsq := Real.sq_sqrt (mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2))
  apply Complex.ext
  · change (1 - 2 * t.val) * (1 - 2 * t.val) -
      (-(2 * Real.sqrt (t.val * (1 - t.val)))) *
        (2 * Real.sqrt (t.val * (1 - t.val))) = 1
    nlinarith
  · change (1 - 2 * t.val) * (2 * Real.sqrt (t.val * (1 - t.val))) +
      (-(2 * Real.sqrt (t.val * (1 - t.val)))) * (1 - 2 * t.val) = 0
    ring

def semicircleUnitary (t : Interval) : unitary ℂ :=
  ⟨semicircleValue t, semicircleValue_star_mul t, by
    rw [mul_comm]; exact semicircleValue_star_mul t⟩

attribute [local fun_prop] Continuous.const_mul continuous_mul_const in
theorem semicircleUnitary_continuous : Continuous semicircleUnitary := by
  apply Continuous.subtype_mk
  change Continuous (fun t : Interval => semicircleValue t)
  simp only [semicircleValue, Complex.mk_eq_add_mul_I]
  fun_prop

@[simp] theorem semicircleUnitary_start : semicircleUnitary start = 1 := by
  apply Subtype.ext
  change semicircleValue start = 1
  apply Complex.ext <;> norm_num [semicircleValue, start]

@[simp] theorem semicircleUnitary_finish : (semicircleUnitary finish : ℂ) = -1 := by
  apply Complex.ext <;> norm_num [semicircleUnitary, semicircleValue, finish]

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def projectionSignPath (P : A) (hP : IsStarProjection P) (t : Interval) : unitary A :=
  projectionPhase P hP (semicircleUnitary t)

theorem projectionSignPath_continuous [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousSMul ℂ A] (P : A) (hP : IsStarProjection P) :
    Continuous (projectionSignPath P hP) := by
  apply Continuous.subtype_mk
  exact continuous_const.add
    ((continuous_subtype_val.comp semicircleUnitary_continuous).smul continuous_const)

@[simp] theorem projectionSignPath_start (P : A) (hP : IsStarProjection P) :
    projectionSignPath P hP start = 1 := by
  apply Subtype.ext
  change 1 - P + (semicircleUnitary start : ℂ) • P = 1
  rw [semicircleUnitary_start]
  simp

@[simp] theorem projectionSignPath_finish (P : A) (hP : IsStarProjection P) :
    (projectionSignPath P hP finish : A) = 1 - (2 : ℂ) • P := by
  change 1 - P + (semicircleUnitary finish : ℂ) • P = _
  rw [semicircleUnitary_finish]
  module

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_InvolutionUnitaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit path from the identity to a self-adjoint involution -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def involutionUnitaryPath (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    Interval → unitary A :=
  projectionSignPath (involutionNegativeProjection U)
    (involutionNegativeProjection_isStarProjection U hU hUU)

theorem involutionUnitaryPath_continuous [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousSMul ℂ A] (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    Continuous (involutionUnitaryPath U hU hUU) := projectionSignPath_continuous _ _

@[simp] theorem involutionUnitaryPath_start (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    involutionUnitaryPath U hU hUU start = 1 := projectionSignPath_start _ _

@[simp] theorem involutionUnitaryPath_finish (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    (involutionUnitaryPath U hU hUU finish : A) = U := by
  change (projectionSignPath (involutionNegativeProjection U)
    (involutionNegativeProjection_isStarProjection U hU hUU) finish : A) = U
  rw [projectionSignPath_finish]
  unfold involutionNegativeProjection
  rw [smul_smul]
  norm_num

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_PartialIsometryDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Swapping two isometric images by a partial-isometry dilation -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

/-- A continuous path from one to the symmetry exchanging the two images. -/
def partialIsometryDilationPath (T : A) (hT : T * star T * T = T) :
    Interval → unitary (Matrix (Fin 2) (Fin 2) A) :=
  involutionUnitaryPath (partialIsometryDilation T) (partialIsometryDilation_selfAdjoint T)
    (partialIsometryDilation_sq T hT)

theorem partialIsometryDilationPath_continuous (T : A) (hT : T * star T * T = T) :
    Continuous (partialIsometryDilationPath T hT) := involutionUnitaryPath_continuous _ _ _

@[simp] theorem partialIsometryDilationPath_start (T : A) (hT : T * star T * T = T) :
    partialIsometryDilationPath T hT start = 1 := involutionUnitaryPath_start _ _ _

@[simp] theorem partialIsometryDilationPath_finish (T : A) (hT : T * star T * T = T) :
    (partialIsometryDilationPath T hT finish).val = partialIsometryDilation T :=
  involutionUnitaryPath_finish _ _ _

theorem partialIsometryDilation_conjugation (T f : A) (hT : T * star T * T = T)
    (hleft : (star T * T) * f = f) (hright : f * (star T * T) = f) :
    partialIsometryDilation T * !![1 + f, 0; 0, 1] * partialIsometryDilation T =
      !![1, 0; 0, 1 + T * f * star T] := by
  obtain ⟨hE, hF, hEs, hsF, hTE, hFT⟩ := partialIsometry_complement_relations T hT
  have hEf : (1 - star T * T) * f = 0 := by rw [sub_mul, one_mul, hleft, sub_self]
  have hfE : f * (1 - star T * T) = 0 := by rw [mul_sub, mul_one, hright, sub_self]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change ((1 - star T * T) * (1 + f) + star T * 0) * (1 - star T * T) +
      ((1 - star T * T) * 0 + star T * 1) * T = 1
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, hEf]
    rw [hE]
    abel
  · change ((1 - star T * T) * (1 + f) + star T * 0) * star T +
      ((1 - star T * T) * 0 + star T * 1) * (1 - T * star T) = 0
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, hEf, hEs, hsF]
  · change (T * (1 + f) + (1 - T * star T) * 0) * (1 - star T * T) +
      (T * 0 + (1 - T * star T) * 1) * T = 0
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, add_mul, mul_assoc, hfE, hTE, hFT]
  · change (T * (1 + f) + (1 - T * star T) * 0) * star T +
      (T * 0 + (1 - T * star T) * 1) * (1 - T * star T) = 1 + T * f * star T
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, add_mul, hF]
    noncomm_ring

end CoarseAssembly.Analytic

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

theorem orthogonal_isometries_decompose (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hex : V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint +
      W.toContinuousLinearMap.comp W.toContinuousLinearMap.adjoint = 1)
    (T : H →L[ℂ] H) (S : E →L[ℂ] E) (R : F →L[ℂ] F)
    (hV : T.comp V.toContinuousLinearMap = V.toContinuousLinearMap.comp S)
    (hW : T.comp W.toContinuousLinearMap = W.toContinuousLinearMap.comp R) :
    T = operatorConjugation V S + operatorConjugation W R := by
  ext x
  have hx : V (V.toContinuousLinearMap.adjoint x) + W (W.toContinuousLinearMap.adjoint x) = x :=
    DFunLike.congr_fun hex x
  change T x = V (S (V.toContinuousLinearMap.adjoint x)) + W (R (W.toContinuousLinearMap.adjoint x))
  calc
    _ = T (V (V.toContinuousLinearMap.adjoint x) + W (W.toContinuousLinearMap.adjoint x)) :=
      congrArg T hx.symm
    _ = _ := by
      rw [map_add]
      exact congrArg₂ (fun x y : H => x + y)
        (DFunLike.congr_fun hV (V.toContinuousLinearMap.adjoint x))
        (DFunLike.congr_fun hW (W.toContinuousLinearMap.adjoint x))

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

omit [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (G i)] in
theorem blockOperator_intertwines (V : ∀ i, E i →ₗᵢ[ℂ] G i)
    (A : ∀ i, E i →L[ℂ] E i) (B : ∀ i, G i →L[ℂ] G i)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (hV : ∀ i, (B i).comp (V i).toContinuousLinearMap = (V i).toContinuousLinearMap.comp (A i)) :
    (blockOperator B D hD hB).comp (blockIsometry V).toContinuousLinearMap =
      (blockIsometry V).toContinuousLinearMap.comp (blockOperator A C hC hA) := by
  ext v i
  exact DFunLike.congr_fun (hV i) (v i)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm continuity of the rational boundary representative -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A P : Type*} [CStarAlgebra A] [TopologicalSpace P]

theorem continuous_rationalBoundaryUnitary (F : P → A) (hF : ∀ p, IsSelfAdjoint (F p))
    (hcont : Continuous F) :
    Continuous (fun p => (rationalBoundaryUnitary (F p) (hF p) : A)) := by
  have hc := continuous_cayleyUnitary F hF hcont
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul]
  convert! (hc.mul hc).neg

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational boundary respects bounded intertwiners

This includes restriction to a component of a Hilbert direct sum. No
multiplicativity of compression on arbitrary operators is assumed.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem cayleyDenominator_intertwines (R : H →L[ℂ] K) (F : H →L[ℂ] H) (G : K →L[ℂ] K)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((cayleyDenominator F hF : H →L[ℂ] H) x) =
      (cayleyDenominator G hG : K →L[ℂ] K) (R x) := by
  simp only [cayleyDenominator_val, Algebra.algebraMap_eq_smul_one,
    add_apply, smul_apply,
    one_apply_eq_self, map_add, map_smul, h]

theorem cayleyDenominator_inv_intertwines (R : H →L[ℂ] K) (F : H →L[ℂ] H) (G : K →L[ℂ] K)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((↑(cayleyDenominator F hF)⁻¹ : H →L[ℂ] H) x) =
      (↑(cayleyDenominator G hG)⁻¹ : K →L[ℂ] K) (R x) := by
  let b := cayleyDenominator F hF
  let d := cayleyDenominator G hG
  have hleft (y : K) : (↑d⁻¹ : K →L[ℂ] K) ((d : K →L[ℂ] K) y) = y := by
    change ((↑d⁻¹ : K →L[ℂ] K) * (d : K →L[ℂ] K)) y = y
    rw [Units.inv_mul, one_apply_eq_self]
  have hright (y : H) : (b : H →L[ℂ] H) ((↑b⁻¹ : H →L[ℂ] H) y) = y := by
    change ((b : H →L[ℂ] H) * (↑b⁻¹ : H →L[ℂ] H)) y = y
    rw [Units.mul_inv, one_apply_eq_self]
  calc
    R ((↑b⁻¹ : H →L[ℂ] H) x) = (↑d⁻¹ : K →L[ℂ] K) ((d : K →L[ℂ] K) (R ((↑b⁻¹ : H →L[ℂ] H) x))) :=
      (hleft _).symm
    _ = (↑d⁻¹ : K →L[ℂ] K) (R ((b : H →L[ℂ] H) ((↑b⁻¹ : H →L[ℂ] H) x))) := by
      rw [cayleyDenominator_intertwines R F G hF hG h]
    _ = (↑d⁻¹ : K →L[ℂ] K) (R x) := by rw [hright]

theorem cayleyUnitary_intertwines (R : H →L[ℂ] K) (F : H →L[ℂ] H) (G : K →L[ℂ] K)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((cayleyUnitary F hF : H →L[ℂ] H) x) = (cayleyUnitary G hG : K →L[ℂ] K) (R x) := by
  simp only [cayleyUnitary_val, cayleyDenominator_star,
    Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp,
    sub_apply, smul_apply,
    one_apply_eq_self, map_sub, map_smul, h]
  rw [cayleyDenominator_inv_intertwines R F G hF hG h]

theorem rationalBoundaryUnitary_intertwines (R : H →L[ℂ] K)
    (F : H →L[ℂ] H) (G : K →L[ℂ] K) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((rationalBoundaryUnitary F hF : H →L[ℂ] H) x) =
      (rationalBoundaryUnitary G hG : K →L[ℂ] K) (R x) := by
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul,
    neg_apply, mul_apply_eq_comp, map_neg]
  rw [cayleyUnitary_intertwines R F G hF hG h,
    cayleyUnitary_intertwines R F G hF hG h]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyNormControl
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform Lipschitz estimate for the rational boundary unitary -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem cayleyDenominator_inverse_identity (F : A) (hF : IsSelfAdjoint F) :
    (2 * Complex.I : ℂ) • (↑(cayleyDenominator F hF)⁻¹ : A) =
      1 - (cayleyUnitary F hF : A) := by
  have hscalar : algebraMap ℂ A (2 * Complex.I) =
      (cayleyDenominator F hF : A) - star (cayleyDenominator F hF : A) := by
    rw [cayleyDenominator_star, cayleyDenominator_val, map_mul]
    simp only [map_ofNat]
    noncomm_ring
  rw [Algebra.smul_def, hscalar, sub_mul, Units.mul_inv, cayleyUnitary_val]

theorem cayleyDenominator_inverse_norm_le (F : A) (hF : IsSelfAdjoint F) :
    ‖(↑(cayleyDenominator F hF)⁻¹ : A)‖ ≤ 1 := by
  nontriviality A
  have h := norm_sub_le (1 : A) (cayleyUnitary F hF : A)
  rw [← cayleyDenominator_inverse_identity F hF, norm_smul, norm_mul,
    Complex.norm_I, norm_one, CStarRing.norm_coe_unitary] at h
  norm_num at h
  linarith

theorem cayleyDenominator_inverse_sub_norm_le (F G : A)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    ‖(↑(cayleyDenominator F hF)⁻¹ : A) - ↑(cayleyDenominator G hG)⁻¹‖ ≤ ‖F - G‖ := by
  let u := cayleyDenominator F hF
  let v := cayleyDenominator G hG
  have he : (↑u⁻¹ : A) - ↑v⁻¹ = ↑u⁻¹ * (G - F) * ↑v⁻¹ := by
    have hdiff : G - F = (v : A) - u := by
      simp only [u, v, cayleyDenominator_val, add_sub_add_right_eq_sub]
    rw [hdiff, mul_sub, sub_mul]
    rw [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul, one_mul]
  rw [he]
  calc
    _ ≤ ‖(↑u⁻¹ : A)‖ * ‖G - F‖ * ‖(↑v⁻¹ : A)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖G - F‖ * 1 := by
      gcongr
      · exact cayleyDenominator_inverse_norm_le F hF
      · exact cayleyDenominator_inverse_norm_le G hG
    _ = ‖F - G‖ := by rw [one_mul, mul_one, norm_sub_rev]

theorem cayleyUnitary_sub_norm_le (F G : A) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    ‖(cayleyUnitary F hF : A) - cayleyUnitary G hG‖ ≤ 2 * ‖F - G‖ := by
  have he : (cayleyUnitary F hF : A) - cayleyUnitary G hG =
      -(2 * Complex.I : ℂ) •
        ((↑(cayleyDenominator F hF)⁻¹ : A) - ↑(cayleyDenominator G hG)⁻¹) := by
    rw [neg_smul, smul_sub, cayleyDenominator_inverse_identity,
      cayleyDenominator_inverse_identity]
    abel
  rw [he, norm_smul, norm_neg, norm_mul, Complex.norm_I]
  norm_num only [Complex.norm_ofNat, mul_one]
  exact mul_le_mul_of_nonneg_left (cayleyDenominator_inverse_sub_norm_le F G hF hG) (by norm_num)

theorem rationalBoundaryUnitary_sub_norm_le (F G : A)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    ‖(rationalBoundaryUnitary F hF : A) - rationalBoundaryUnitary G hG‖ ≤ 4 * ‖F - G‖ := by
  nontriviality A
  let u : A := cayleyUnitary F hF
  let v : A := cayleyUnitary G hG
  have hu : ‖u‖ = 1 := CStarRing.norm_coe_unitary _
  have hv : ‖v‖ = 1 := CStarRing.norm_coe_unitary _
  have he : -(u * u) - -(v * v) = (v - u) * v + u * (v - u) := by
    rw [neg_sub_neg, sub_mul, mul_sub, sub_add_sub_cancel]
  change ‖-(u * u) - -(v * v)‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(v - u) * v‖ + ‖u * (v - u)‖ := norm_add_le _ _
    _ ≤ ‖v - u‖ * ‖v‖ + ‖u‖ * ‖v - u‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖u - v‖ := by rw [hu, hv, norm_sub_rev]; ring
    _ ≤ 2 * (2 * ‖F - G‖) := mul_le_mul_of_nonneg_left (cayleyUnitary_sub_norm_le F G hF hG) (by norm_num)
    _ = _ := by ring

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CharacterExtension
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing a represented subspace using a character

For a unital coefficient algebra with a character, the complement of the
represented subspace can carry that character. The cut-down operator acts
as the identity there, so this completion preserves the Fredholm defects.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {H : HilbertSpace}

def characterProjectionRepresentation (χ : A →⋆ₐ[ℂ] ℂ) (P : End H)
    (hP : IsStarProjection P) : A →⋆ₙₐ[ℂ] End H where
  toFun a := χ a • P
  map_zero' := by simp
  map_add' a b := by simp [add_smul]
  map_mul' a b := by
    have hPP : P * P = P := hP.isIdempotentElem
    rw [map_mul, smul_mul_assoc, mul_smul_comm, hPP, smul_smul, mul_comm]
  map_smul' z a := by simp [smul_smul]
  map_star' a := by rw [map_star, star_smul, hP.isSelfAdjoint.star_eq]

/-- Any representation with the identity operator is degenerate. -/
def identityOperatorCycle (ρ : A →⋆ₙₐ[ℂ] End H) : OddCycle A where
  space := H
  representation := ρ
  operator := 1
  commutator_compact _ := by simp; exact isCompactOperator_zero
  square_compact _ := by simp; exact isCompactOperator_zero
  adjoint_compact _ := by simp; exact isCompactOperator_zero

theorem identityOperatorCycle_degenerate (ρ : A →⋆ₙₐ[ℂ] End H) :
    (identityOperatorCycle ρ).Degenerate := by
  constructor
  · intro a; change (1 : End H) * ρ a - ρ a * 1 = 0; simp
  constructor
  · intro a; change ((1 : End H) * 1 - 1) * ρ a = 0; simp
  · intro a; change (star (1 : End H) - 1) * ρ a = 0; simp

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ClopenRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting analytic K-homology to a compact open component

Extension by zero is constructed on the actual continuous-function
algebras. Its contravariant action on Fredholm modules is a left inverse
to pushforward of the component inclusion. No additivity theorem is
needed for this restriction calculation.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology
open scoped ZeroAtInfty

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space Y]

def restrictComponent (e : X ↪ Y) (he : IsOpenEmbedding e) :
    LocallyFiniteK1 Y →+ LocallyFiniteK1 X := precomp (zeroExtensionHom e he)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ClopenNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction across a proper map

If the preimage of a compact open component is exactly the specified
compact open component of the source, the corresponding KK restrictions
commute with pushforward. The identity is proved on functions first.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology
open scoped ZeroAtInfty

variable {A B X Y : Type} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace A] [CompactSpace B] [T2Space X] [T2Space Y]

theorem pullback_zeroExtension (e : A ↪ X) (he : IsOpenEmbedding e)
    (d : B ↪ Y) (hd : IsOpenEmbedding d) (f : CocompactMap X Y) (g : CocompactMap A B)
    (commutes : ∀ a, f (e a) = d (g a))
    (preimage : ∀ x, f x ∈ Set.range d ↔ x ∈ Set.range e) :
    (pullback f).comp (zeroExtensionHom d hd) =
      (zeroExtensionHom e he).comp (pullback g) := by
  ext h x
  change zeroExtension d hd h (f x) = zeroExtension e he (pullback g h) x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    rw [commutes, zeroExtension_apply, zeroExtension_apply]
    rfl
  · have hfx : f x ∉ Set.range d := fun h => hx ((preimage x).mp h)
    rw [zeroExtension_apply_outside d hd h hfx, zeroExtension_apply_outside e he _ hx]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactHomotopy
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_finish _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_start _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_finish _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_start _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_finish _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_start _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_finish _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact homotopy invariance in the actual Fredholm presentation

A homotopy of maps gives a point-norm continuous homotopy of pulled-back
representations. Its Fredholm operator stays fixed. This discharges the
homotopy field of the published filling input directly from the definitions.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty CStarAlgebra

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X]

def homotopySlice {f g : C(X, Y)} (F : f.Homotopy g) (t : Interval) : C(X, Y) :=
  F.toContinuousMap.curry t

omit [CompactSpace X] in
@[simp] theorem homotopySlice_start {f g : C(X, Y)} (F : f.Homotopy g) :
    homotopySlice F start = f := by
  ext x
  exact F.map_zero_left x

omit [CompactSpace X] in
@[simp] theorem homotopySlice_finish {f g : C(X, Y)} (F : f.Homotopy g) :
    homotopySlice F finish = g := by
  ext x
  exact F.map_one_left x

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform bound on successive congruence fibers

A residue modulo `2^(k+1)` is determined by its residue modulo `2^k`
and one binary digit. Applying this to the nine matrix entries bounds
every fiber of the special-linear reduction by `2^9`, including `k=0`.
No surjectivity or formula for the order of the group is needed.
-/

namespace CoarseAssembly.Congruence

theorem residue_topBit_injective (k : ℕ) {x y : ZMod (2 ^ (k + 1))}
    (hr : residueMap (Nat.le_succ k) x = residueMap (Nat.le_succ k) y)
    (hb : topBit k x = topBit k y) : x = y := by
  apply ZMod.val_injective
  have hmod := congrArg ZMod.val hr
  have hdiv := congrArg Fin.val hb
  change x.val / 2 ^ k = y.val / 2 ^ k at hdiv
  simp only [residueMap, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] at hmod
  have hx := Nat.mod_add_div x.val (2 ^ k)
  have hy := Nat.mod_add_div y.val (2 ^ k)
  calc
    x.val = x.val % 2 ^ k + 2 ^ k * (x.val / 2 ^ k) := hx.symm
    _ = y.val % 2 ^ k + 2 ^ k * (y.val / 2 ^ k) := by rw [hmod, hdiv]
    _ = y.val := hy

theorem quotient_fiber_code_injective (k : ℕ) {x y : Quotient (k + 1)}
    (hr : quotientMap (Nat.le_succ k) x = quotientMap (Nat.le_succ k) y)
    (hb : matrixTopBits k x = matrixTopBits k y) : x = y := by
  apply Subtype.ext
  ext i j
  apply residue_topBit_injective k
  · exact congrArg (fun q : Quotient k => q.val i j) hr
  · exact congrFun (congrFun hb i) j

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceSurjective
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.holonomyCharge_reduceSteps _root_.OAI.CoarseAssembly.Congruence.holonomyWord_reduceSteps _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surjectivity of the successive special-linear reductions

Lift the entries arbitrarily. The lifted determinant is odd, hence a unit;
rescaling one row by its inverse corrects the determinant without changing
the reduction. Level zero is handled by its singleton group.
-/

namespace CoarseAssembly.Congruence

theorem isUnit_of_residue_one {k : ℕ} (hk : 1 ≤ k) (a : ZMod (2 ^ (k + 1)))
    (ha : residueMap (Nat.le_succ k) a = 1) : IsUnit a := by
  have htwo := congrArg (residueMap hk) ha
  rw [residueMap_comp, map_one] at htwo
  have hval : (a.val : ZMod 2) = 1 := by
    simpa only [residueMap, ZMod.castHom_apply, ZMod.cast_eq_val, pow_one] using htwo
  rw [← ZMod.natCast_zmod_val a]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (Nat.succ_pos k)).2
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff a.val 2).2 hd
  exact zero_ne_one (hz.symm.trans hval)

theorem quotientMap_successor_surjective (k : ℕ) :
    Function.Surjective (quotientMap (Nat.le_succ k)) := by
  intro q
  by_cases hk : k = 0
  · subst k
    exact ⟨1, Subsingleton.elim _ _⟩
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  let φ := residueMap (Nat.le_succ k)
  let A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ (k + 1))) :=
    fun i j => (q.val i j).val
  have hA : φ.mapMatrix A = q.val := by
    ext i j
    change φ ((q.val i j).val : ZMod (2 ^ (k + 1))) = q.val i j
    simp
  have hdet : φ A.det = 1 := by
    rw [RingHom.map_det, hA]
    exact q.property
  obtain ⟨u, hu⟩ := isUnit_of_residue_one hk1 A.det hdet
  let D : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ (k + 1))) :=
    Matrix.diagonal ![(u⁻¹ : (ZMod (2 ^ (k + 1)))ˣ), 1, 1]
  have hDdet : (D * A).det = 1 := by
    simp [D, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_succ, ← hu]
  have huφ : Units.map φ.toMonoidHom u = 1 := by
    apply Units.ext
    change φ (u : ZMod (2 ^ (k + 1))) = 1
    rw [hu]
    exact hdet
  have hinv : φ ((u⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) = 1 := by
    change ((Units.map φ.toMonoidHom u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = 1
    rw [map_inv, huφ]
    rfl
  have hD : φ.mapMatrix D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Matrix.diagonal, hinv]
  refine ⟨⟨D * A, hDdet⟩, ?_⟩
  apply Subtype.ext
  change φ.mapMatrix (D * A) = q.val
  rw [map_mul, hD, hA, one_mul]

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceEdgeOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete one-step congruence-fiber operators

The normalized child map is now instantiated with the proved surjective
congruence reduction. Its adjoint and the equal-depth permutations preserve
constants and have coefficients supported precisely on the prescribed
right-holonomy edge relation.
-/

noncomputable section

namespace CoarseAssembly.Congruence

def childIsometry (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    lp (fun _ : Quotient k => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : Quotient (k + 1) => ℂ) 2 := by
  classical
  exact twistedQuotientCopy (quotientMap (Nat.le_succ k))
    (quotientMap_successor_surjective k) (holonomy t k ^ a)

theorem childIsometry_constant (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    childIsometry t k a (fiberConstant (Quotient k) (1 : ℂ)) =
      fiberConstant (Quotient (k + 1)) 1 := by
  classical
  exact twistedQuotientCopy_constant _ _ _

theorem childAdjoint_constant (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    (childIsometry t k a).toContinuousLinearMap.adjoint
        (fiberConstant (Quotient (k + 1)) (1 : ℂ)) =
      fiberConstant (Quotient k) 1 := by
  rw [← childIsometry_constant t k a, adjoint_apply_isometry]

theorem childIsometry_support (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ)
    (q : Quotient k) (z : Quotient (k + 1))
    (hne : quotientMap (Nat.le_succ k) z ≠ q * holonomy t k ^ a) :
    childIsometry t k a (lp.single 2 q (1 : ℂ)) z = 0 := by
  classical
  let f := quotientMap (Nat.le_succ k)
  change twistedQuotientCopy f (quotientMap_successor_surjective k) (holonomy t k ^ a)
    (lp.single 2 q 1) z = 0
  rw [twistedQuotientCopy_apply]
  have harg : f z * (holonomy t k ^ a)⁻¹ ≠ q := by
    intro he
    apply hne
    calc
      f z = (f z * (holonomy t k ^ a)⁻¹) * holonomy t k ^ a := by group
      _ = q * holonomy t k ^ a := by rw [he]
  rw [lp.single_apply_ne 2 q 1 harg, mul_zero]

theorem childAdjoint_support (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ)
    (q : Quotient k) (z : Quotient (k + 1))
    (hne : quotientMap (Nat.le_succ k) z ≠ q * holonomy t k ^ a) :
    (childIsometry t k a).toContinuousLinearMap.adjoint (lp.single 2 z (1 : ℂ)) q = 0 := by
  have he := ContinuousLinearMap.adjoint_inner_right
    (childIsometry t k a).toContinuousLinearMap (lp.single 2 q 1) (lp.single 2 z 1)
  simp only [lp.inner_single_left, lp.inner_single_right] at he
  change inner ℂ (1 : ℂ) (_) = inner ℂ (childIsometry t k a (lp.single 2 q 1) z) 1 at he
  rw [childIsometry_support t k a q z hne] at he
  simpa only [RCLike.inner_apply, map_one, map_zero, mul_one, mul_zero, inner_zero_left] using he

def sameLevelIsometry (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    lp (fun _ : Quotient k => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Quotient k => ℂ) 2 :=
  reindexFiber (Equiv.mulRight (holonomy t k ^ a))

theorem sameLevelIsometry_constant (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ) :
    sameLevelIsometry t k a (fiberConstant (Quotient k) (1 : ℂ)) =
      fiberConstant (Quotient k) 1 := reindexFiber_constant _ _

theorem sameLevelIsometry_support (t : ℤ_[2]ˣ) (k : ℕ) (a : ℤ)
    (q z : Quotient k) (hne : z ≠ q * holonomy t k ^ a) :
    sameLevelIsometry t k a (lp.single 2 q (1 : ℂ)) z = 0 := by
  change (lp.single (E := fun _ : Quotient k => ℂ) 2 q 1)
    (z * (holonomy t k ^ a)⁻¹) = 0
  apply lp.single_apply_ne
  intro he
  apply hne
  calc
    z = (z * (holonomy t k ^ a)⁻¹) * holonomy t k ^ a := by group
    _ = q * holonomy t k ^ a := by rw [he]

end CoarseAssembly.Congruence

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DiagonalBoundaryCoordinates
attribute [-simp] _root_.OAI.CoarseAssembly.DiscreteRoe.coefficientIsometry_apply _root_.OAI.CoarseAssembly.DiscreteRoe.conjugationHom_apply _root_.OAI.CoarseAssembly.DiscreteRoe.constantBlock_apply _root_.OAI.CoarseAssembly.DiscreteRoe.coordinate_partitionMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionIsometry_toContinuousLinearMap _root_.OAI.CoarseAssembly.DiscreteRoe.partitionMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates of the whole-union rational boundary unitary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rowRestriction (i : ℕ) : Module (Sigma V) H →L[ℂ] Module (V i) H :=
  (lp.evalCLM ℂ (fun j => Module (V j) H) 2 i).comp
    (flattenEquiv (Q := V) (H := H)).symm.toLinearIsometry.toContinuousLinearMap

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
@[simp] theorem rowRestriction_apply (i : ℕ) (v : Module (Sigma V) H) :
    rowRestriction i v = rowVector v i := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ToeplitzProductIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicativity of Toeplitz compression modulo compact operators -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem toeplitzCompression_index_mul (P U V : End H) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hVl : star V * V = 1) (hVr : V * star V = 1)
    (hU : IsCompactOperator (P * U - U * P : End H))
    (hV : IsCompactOperator (P * V - V * P : End H)) :
    (toeplitzCompression P (U * V)).toLinearMap.index =
      (toeplitzCompression P U).toLinearMap.index + (toeplitzCompression P V).toLinearMap.index := by
  have hUVl : star (U * V) * (U * V) = 1 := by
    calc
      _ = star V * (star U * U) * V := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hUl, mul_one, hVl]
  have hUVr : (U * V) * star (U * V) = 1 := by
    calc
      _ = U * (V * star V) * star U := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hVr, mul_one, hUr]
  have hUV := compact_commutator_mul P U V hU hV
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects P (U * V) hP hPP hUVl hUVr hUV
  have hK := toeplitzCompression_product_compact P U V hPP hV
  have hKs : IsCompactOperator (star (toeplitzCompression P U * toeplitzCompression P V -
      toeplitzCompression P (U * V)) : End H) := by
    rw [star_sub, star_mul, toeplitzCompression_star P U hP,
      toeplitzCompression_star P V hP, toeplitzCompression_star P (U * V) hP, star_mul]
    exact toeplitzCompression_product_compact P (star V) (star U) hPP
      (compact_commutator_star_unitary P U hUl hUr hU)
  have hi := fredholmIndex_compactPerturb (toeplitzCompression P (U * V))
    (toeplitzCompression P U * toeplitzCompression P V - toeplitzCompression P (U * V)) hl hr hK hKs
  have he : toeplitzCompression P (U * V) +
      (toeplitzCompression P U * toeplitzCompression P V - toeplitzCompression P (U * V)) =
        toeplitzCompression P U * toeplitzCompression P V := by abel
  rw [he] at hi
  exact hi.trans ((toeplitzCompression_fredholm P U hP hPP hUl hUr hU).index_comp
    (toeplitzCompression_fredholm P V hP hPP hVl hVr hV))

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EssentialToeplitzIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity of the essentially self-adjoint Toeplitz index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem essentialToeplitz_index_normalize (F N U : End H)
    (hF : IsSelfAdjoint F) (hN : IsSelfAdjoint N) (hNN : N * N = 1)
    (hNF : IsCompactOperator (N - F : End H))
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hFU : IsCompactOperator (F * U - U * F : End H)) :
    (toeplitzCompression (positiveProjection F) U).toLinearMap.index =
      (toeplitzCompression (positiveProjection N) U).toLinearMap.index := by
  have hNU := compact_commutator_of_compact_change F N U hNF hFU
  have hQU : IsCompactOperator (positiveProjection N * U - U * positiveProjection N : End H) := by
    rw [positiveProjection_commutator]
    exact hNU.smul (1 / 2 : ℝ)
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects (positiveProjection N) U
    (positiveProjection_selfAdjoint N hN) (positiveProjection_sq N hNN) hUl hUr hQU
  have hPQ : IsCompactOperator (positiveProjection F - positiveProjection N : End H) := by
    rw [positiveProjection_sub, show F - N = -(N - F) by abel]
    exact hNF.neg.smul (1 / 2 : ℝ)
  have hi := fredholmIndex_compactPerturb (toeplitzCompression (positiveProjection N) U)
    (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U)
    hl hr (compact_toeplitz_sub _ _ _ hPQ)
    (compact_star_toeplitz_sub _ _ _ (positiveProjection_selfAdjoint F hF)
      (positiveProjection_selfAdjoint N hN) hPQ)
  have he : toeplitzCompression (positiveProjection N) U +
      (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U) =
        toeplitzCompression (positiveProjection F) U := by abel
  rw [he] at hi
  exact hi.symm

theorem essentialToeplitz_index_mul (F U V : End H) (hF : IsSelfAdjoint F)
    (hFF : IsCompactOperator (F * F - 1 : End H))
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hVl : star V * V = 1) (hVr : V * star V = 1)
    (hU : IsCompactOperator (F * U - U * F : End H))
    (hV : IsCompactOperator (F * V - V * F : End H)) :
    (toeplitzCompression (positiveProjection F) (U * V)).toLinearMap.index =
      (toeplitzCompression (positiveProjection F) U).toLinearMap.index +
      (toeplitzCompression (positiveProjection F) V).toLinearMap.index := by
  obtain ⟨N, hN, hNN, hNF, _⟩ := exists_compact_involution F hF hFF
  have hUVl : star (U * V) * (U * V) = 1 := by
    calc
      _ = star V * (star U * U) * V := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hUl, mul_one, hVl]
  have hUVr : (U * V) * star (U * V) = 1 := by
    calc
      _ = U * (V * star V) * star U := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hVr, mul_one, hUr]
  rw [essentialToeplitz_index_normalize F N (U * V) hF hN hNN hNF hUVl hUVr
    (compact_commutator_mul F U V hU hV)]
  rw [essentialToeplitz_index_normalize F N U hF hN hNN hNF hUl hUr hU,
    essentialToeplitz_index_normalize F N V hF hN hNN hNF hVl hVr hV]
  apply toeplitzCompression_index_mul _ _ _ (positiveProjection_selfAdjoint N hN)
    (positiveProjection_sq N hNN) hUl hUr hVl hVr
  · rw [positiveProjection_commutator]
    exact (compact_commutator_of_compact_change F N U hNF hU).smul (1 / 2 : ℝ)
  · rw [positiveProjection_commutator]
    exact (compact_commutator_of_compact_change F N V hNF hV).smul (1 / 2 : ℝ)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberedGraph
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.mem_fiberedNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite graph with congruence fibers

The inter-fiber edge relation is written at the common shallower level.
This uniformly describes the equal-depth, parent and child cases. The
generating set is symmetrized and contains the identity to record pure
base moves in a common list of left/right operations.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem one_mem_symmetricMoves (S : Finset ArithmeticGroup) : 1 ∈ symmetricMoves S := by
  simp [symmetricMoves]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaFunctionNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decay of compact-component norms for functions vanishing at infinity -/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology Filter
open scoped ZeroAtInfty

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]

theorem sigmaFunctionRestriction_norm_tendsto (f : C₀(Sigma Y, ℂ)) :
    Tendsto (fun j => ‖sigmaFunctionRestriction Y j f‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : {x : Sigma Y | dist (f x) 0 < ε / 2} ∈ cocompact (Sigma Y) :=
    Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (by positivity)
  obtain ⟨K, hK, hbound⟩ := mem_cocompact.mp hsmall
  obtain ⟨s, t, hs, _ht, hKs⟩ := hK.sigma_exists_finite_sigma_eq
  obtain ⟨N, hN⟩ := hs.bddAbove
  refine ⟨N + 1, fun j hj => ?_⟩
  have hjout : j ∉ s := by
    intro hjs
    have := hN hjs
    omega
  have hnorm : ‖sigmaFunctionRestriction Y j f‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ε / 2)).mpr
    intro x
    have hxout : (⟨j, x⟩ : Sigma Y) ∉ K := by
      rw [← hKs]
      intro hx
      exact hjout hx.1
    have h := hbound hxout
    change dist (f ⟨j, x⟩) 0 < ε / 2 at h
    simpa only [sigmaFunctionRestriction_apply, dist_zero_right] using h.le
  rw [dist_zero_right, norm_norm]
  exact hnorm.trans_lt (by linarith)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycle
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply
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

theorem norm_commutator_le (F T : End H) : ‖F * T - T * F‖ ≤ 2 * ‖F‖ * ‖T‖ := by
  calc
    _ ≤ ‖F * T‖ + ‖T * F‖ := norm_sub_le _ _
    _ ≤ ‖F‖ * ‖T‖ + ‖T‖ * ‖F‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
variable (c : ∀ j, OddCycle C(Y j, ℂ))
variable (M : ℝ) (hM : 0 ≤ M) (hF : ∀ j, ‖(c j).operator‖ ≤ M)

def sigmaCycleOperator : End (countableHilbertSpace (cycleHilbertFamily Y c)) :=
  CoarseAssembly.blockOperator (fun j => (c j).operator) M hM hF

theorem sigmaCycleOperator_selfAdjoint (hself : ∀ j, IsSelfAdjoint (c j).operator) :
    IsSelfAdjoint (sigmaCycleOperator Y c M hM hF) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr (fun j => (hself j).isSymmetric (x j) (y j))

theorem sigmaCycleOperator_sq (hsq : ∀ j, (c j).operator * (c j).operator = 1) :
    sigmaCycleOperator Y c M hM hF * sigmaCycleOperator Y c M hM hF = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  exact DFunLike.congr_fun (hsq j) (x j)

def sigmaCommutatorBlocks (f : C₀(Sigma Y, ℂ)) (j : ℕ) : End (c j).space :=
  (c j).operator * (c j).representation (sigmaFunctionRestriction Y j f) -
    (c j).representation (sigmaFunctionRestriction Y j f) * (c j).operator

include hM hF in
theorem sigmaCommutator_norm (f : C₀(Sigma Y, ℂ)) (j : ℕ) :
    ‖sigmaCommutatorBlocks Y c f j‖ ≤ (2 * M) * ‖sigmaFunctionRestriction Y j f‖ := by
  apply (norm_commutator_le _ _).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hF j) (by norm_num))
    (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)
    (mul_nonneg (by norm_num) hM)

include hM hF in
theorem sigmaCommutator_uniform_bound (f : C₀(Sigma Y, ℂ)) (j : ℕ) :
    ‖sigmaCommutatorBlocks Y c f j‖ ≤ (2 * M) * ‖f‖ :=
  (sigmaCommutator_norm Y c M hM hF f j).trans
    (mul_le_mul_of_nonneg_left (sigmaFunctionRestriction_norm_le Y j f) (by positivity))

include hM hF in
theorem sigmaCommutator_norm_tendsto (f : C₀(Sigma Y, ℂ)) :
    Tendsto (fun j => ‖sigmaCommutatorBlocks Y c f j‖) atTop (𝓝 0) := by
  have hb : Tendsto (fun j => (2 * M) * ‖sigmaFunctionRestriction Y j f‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (sigmaFunctionRestriction_norm_tendsto Y f)
  exact squeeze_zero (fun j => norm_nonneg _) (sigmaCommutator_norm Y c M hM hF f) hb

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UniformCycleNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly bounded representatives for countable families -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

theorem involution_norm_le_one {H : HilbertSpace} (F : End H)
    (hself : IsSelfAdjoint F) (hsq : F * F = 1) : ‖F‖ ≤ 1 := by
  have he : ‖F‖ ^ 2 = ‖(1 : End H)‖ := by
    rw [← hself.norm_mul_self, hsq]
  have hi : ‖(1 : End H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg F]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteHeadNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly controlled involutive replacement of a finite head -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [SecondCountableTopology H]


structure FiniteHeadReplacement (J : Finset ℕ) (A : ∀ i, Operator (V i) H) (C r : ℝ) where
  operator : ∀ i, Operator (V i) H
  selfAdjoint : ∀ i, IsSelfAdjoint (operator i)
  norm_le : ∀ i, ‖operator i‖ ≤ max C 1
  propagation : ∀ i, PropagationLE (max r (finiteHeadRadius (V := V) J)) (operator i)
  compact_diff : ∀ i, IsCompactOperator (operator i - A i)
  involutive : ∀ i, i ∈ J → operator i * operator i = 1
  tail : ∀ i, i ∉ J → operator i = A i

omit [SecondCountableTopology H] in
theorem FiniteHeadReplacement.square_compact {J : Finset ℕ} {A : ∀ i, Operator (V i) H} {C r : ℝ}
    (d : FiniteHeadReplacement J A C r)
    (hc : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) (i : ℕ) :
    IsCompactOperator (d.operator i * d.operator i - (1 : Operator (V i) H)) := by
  by_cases hi : i ∈ J
  · rw [d.involutive i hi, sub_self]
    change IsCompactOperator (0 : Module (V i) H → Module (V i) H)
    exact isCompactOperator_zero
  · rw [d.tail i hi]
    exact hc i

end CoarseAssembly.DiscreteRoe

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HomogeneousReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing repeated Hilbert summands for finite telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : HilbertSpace)

/-- Rotate the first `N+1` coordinates, leaving the infinite tail fixed. -/
def rotatePrefix (N : ℕ) : ℕ ≃ ℕ where
  toFun j := if j = 0 then N else if j ≤ N then j - 1 else j
  invFun j := if j < N then j + 1 else if j = N then 0 else j
  left_inv j := by
    dsimp only
    by_cases h0 : j = 0
    · subst j
      simp
    by_cases hj : j ≤ N
    · have hlt : j - 1 < N := by omega
      simp only [ite_eq_right h0, ite_eq_left hj, ite_eq_left hlt]
      omega
    · have hnj : ¬j < N := by omega
      have hne : j ≠ N := by omega
      simp [h0, hj, hnj, hne]
  right_inv j := by
    dsimp only
    by_cases hj : j < N
    · have hle : j + 1 ≤ N := by omega
      simp [hj, hle]
    · by_cases he : j = N
      · subst j
        simp
      · have h0 : j ≠ 0 := by omega
        have hle : ¬j ≤ N := by omega
        simp [hj, he, h0, hle]

@[simp] theorem rotatePrefix_zero (N : ℕ) : rotatePrefix N 0 = N := by simp [rotatePrefix]

theorem rotatePrefix_inverse_lt (N j : ℕ) (hj : j < N) :
    (rotatePrefix N).symm j = j + 1 := by simp [rotatePrefix, hj]

@[simp] theorem rotatePrefix_inverse_last (N : ℕ) : (rotatePrefix N).symm N = 0 := by
  simp [rotatePrefix]

theorem rotatePrefix_inverse_gt (N j : ℕ) (hj : N < j) :
    (rotatePrefix N).symm j = j := by
  simp [rotatePrefix, not_lt.mpr hj.le, ne_of_gt hj]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledHomotopyDecomposition
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint and interior decompositions of finite homotopy samples -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

/-- Put the last endpoint first, leaving the interior list in its original order. -/
def lastEndpointFirst (N : ℕ) (τ : ℕ → Interval) (j : ℕ) : Interval :=
  if j = 0 then τ (N + 1) else τ j

@[simp] theorem lastEndpointFirst_zero (N : ℕ) (τ : ℕ → Interval) :
    lastEndpointFirst N τ 0 = τ (N + 1) := by simp [lastEndpointFirst]

@[simp] theorem lastEndpointFirst_succ (N : ℕ) (τ : ℕ → Interval) (j : ℕ) :
    lastEndpointFirst N τ (j + 1) = τ (j + 1) := by simp [lastEndpointFirst]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TransferCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-fiber Roe transfer criterion

This proves the operator statement of Proposition 5.1. The required
finite-propagation scalar contractions between fibers are amplified here;
the bounded lift, compactness and compression are constructed, not assumed.
The concrete graph family still has to supply these fiber contractions and
the averaging approximants.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe
open scoped Topology

variable {D : Type*} [DecidableEq D] [PseudoMetricSpace D]

variable {Q : D → Type*} [∀ u, Fintype (Q u)] [∀ u, Nonempty (Q u)]
variable [∀ u, DecidableEq (Q u)] [PseudoMetricSpace (Sigma Q)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Uniform controlled scalar maps preserving the normalized constants. -/
def ControlledFiberMaps (Q : D → Type*) [∀ u, Fintype (Q u)]
    [∀ u, DecidableEq (Q u)] [PseudoMetricSpace (Sigma Q)] : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ s : ℝ, 0 ≤ s ∧
    ∃ O : ∀ u v, lp (fun _ : Q v => ℂ) 2 →L[ℂ] lp (fun _ : Q u => ℂ) 2,
      ∀ u v, dist u v ≤ R →
        ‖O u v‖ ≤ 1 ∧ O u v (fiberConstant (Q v) (1 : ℂ)) = fiberConstant (Q u) 1 ∧
        ∀ q r, s < dist (⟨u, q⟩ : Sigma Q) ⟨v, r⟩ → O u v (lp.single 2 r 1) q = 0

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycleRestriction
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

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, T2Space (Y j)]

theorem sigmaRestriction_extension_same (j : ℕ) (f : C₀(Y j, ℂ)) :
    sigmaFunctionRestriction Y j
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) =
      compactFunctionForget f := by
  ext x
  exact zeroExtension_apply (sigmaComponent Y j) (sigmaComponent_open Y j) f x

theorem sigmaRestriction_extension_ne (j k : ℕ) (hjk : j ≠ k) (f : C₀(Y j, ℂ)) :
    sigmaFunctionRestriction Y k
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) = 0 := by
  ext x
  apply zeroExtension_apply_outside (sigmaComponent Y j) (sigmaComponent_open Y j) f
  rintro ⟨y, hy⟩
  exact hjk (congrArg Sigma.fst hy)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UniformSubdivision
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.homotopySlice_finish _root_.OAI.CoarseAssembly.Analytic.homotopySlice_start _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_finish _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_start _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_succ _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_zero _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_finish _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_start _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_finish _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_start _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_finish _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite subdivisions of an actual norm-continuous homotopy -/

noncomputable section

namespace CoarseAssembly.Analytic

def intervalGrid (N : ℕ) (hN : 0 < N) (j : ℕ) : Interval :=
  ⟨((min j N : ℕ) : ℝ) / N, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast Nat.min_le_right j N)⟩

@[simp] theorem intervalGrid_start (N : ℕ) (hN : 0 < N) : intervalGrid N hN 0 = start := by
  apply Subtype.ext
  simp [intervalGrid, start]

@[simp] theorem intervalGrid_finish (N : ℕ) (hN : 0 < N) : intervalGrid N hN N = finish := by
  apply Subtype.ext
  simp [intervalGrid, finish, Nat.ne_of_gt hN]

theorem intervalGrid_dist (N : ℕ) (hN : 0 < N) (j : ℕ) (hj : j < N) :
    dist (intervalGrid N hN (j + 1)) (intervalGrid N hN j) = (N : ℝ)⁻¹ := by
  change |((min (j + 1) N : ℕ) : ℝ) / N - ((min j N : ℕ) : ℝ) / N| = _
  rw [Nat.min_eq_left (Nat.succ_le_of_lt hj), Nat.min_eq_left hj.le, Nat.cast_succ]
  have he : ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N := by ring
  rw [he, abs_of_nonneg (by positivity), one_div]

theorem exists_interval_subdivision {E : Type*} [PseudoMetricSpace E]
    (f : Interval → E) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ j, j < N →
      dist (f (intervalGrid N hN (j + 1))) (f (intervalGrid N hN j)) < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨N, hN, hn⟩ := Real.exists_nat_pos_inv_lt hδ
  refine ⟨N, hN, fun j hj => hclose ?_⟩
  rw [intervalGrid_dist N hN j hj]
  exact hn

end CoarseAssembly.Analytic

end

end OAI
end


