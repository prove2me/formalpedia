-- Prove2me | Definitions.Def_OAIQ229C016
-- name    : OAIQ229C016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T08:00:31.791873+00:00
-- url     : https://prove2.me/theorems/9e4ed5ed-4096-4c01-8d4e-41a154f8d046
-- title:
--   Definitions bundle OAIQ229C016 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 17 definitions and 72 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.circleRepresentation`, `OAI.CoarseAssembly.Analytic.compactCommutant`, `OAI.CoarseAssembly.Analytic.compactFamilyCycleHomotopy`, `OAI.CoarseAssembly.Analytic.compactIndexPairing`, `OAI.CoarseAssembly.Analytic.finiteActiveCycle`, `OAI.CoarseAssembly.Analytic.indexFree`, `OAI.CoarseAssembly.Analytic.indexPairing`, `OAI.CoarseAssembly.Analytic.negativeCircleClass`, `OAI.CoarseAssembly.Analytic.negativeCircleCycle`, `OAI.CoarseAssembly.Analytic.negativeCircleOperator`, `OAI.CoarseAssembly.Analytic.representedIndex`, `OAI.CoarseAssembly.Analytic.representedToeplitz`, `OAI.CoarseAssembly.Analytic.sampledCycle`, `OAI.CoarseAssembly.Analytic.sampledFiniteSum`, `OAI.CoarseAssembly.Analytic.shiftToeplitz`, `OAI.CoarseAssembly.Analytic.shiftToeplitzInverse`, `OAI.CoarseAssembly.circleFundamental`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_BlockOperators`, `CoarseAssembly_CayleyNaturality`, `CoarseAssembly_CayleyNonunitalNaturality`, `CoarseAssembly_CayleyUnitization`, `CoarseAssembly_CircleCoefficient`, `CoarseAssembly_CircleSequenceRepresentation`, `CoarseAssembly_CompactBlockSum`, `CoarseAssembly_CompactFamilyHomotopy`, `CoarseAssembly_CompactIndexPairing`, `CoarseAssembly_DegenerateCutDown`, `CoarseAssembly_DirectSumIndex`, `CoarseAssembly_EssentialCommutant`, `CoarseAssembly_FiniteCycleSum`, `CoarseAssembly_HilbertHeadTail`, `CoarseAssembly_HomogeneousReindex`, `CoarseAssembly_IndexPairing`, `CoarseAssembly_MultiplicativeIndexPairing`, `CoarseAssembly_NegativeCircleCycle`, `CoarseAssembly_NegativeProjection`, `CoarseAssembly_OrthogonalExtensionBoundary`, `CoarseAssembly_RawCycleIndex`, `CoarseAssembly_RepresentedIndex`, `CoarseAssembly_RipsBoundaryDegeneracy`, `CoarseAssembly_SampledHomotopy`, `CoarseAssembly_ShiftIndex`, `CoarseAssembly_UnitaryHomotopyIndex`, `CoarseAssembly_UnitaryIndex`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C009` and `OAIQ229C010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C024`, `OAIQ229C025` and `OAIQ229C026`.
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
import Definitions.Def_OAIQ229C009
import Definitions.Def_OAIQ229C010

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

/-- Uniform fiberwise norm error bounds the operator error on the whole
Hilbert sum. This is the norm estimate for the amplified Kazhdan projection. -/
theorem blockOperator_dist_le (A B : ∀ i, E i →L[ℂ] F i)
    (C D ε : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (hAB : ∀ i, ‖A i - B i‖ ≤ ε) :
    ‖blockOperator A C hC hA - blockOperator B D hD hB‖ ≤ ε := by
  have heq : blockOperator A C hC hA - blockOperator B D hD hB =
      blockOperator (fun i => A i - B i) ε hε hAB := by
    ext x i
    rfl
  rw [heq]
  exact blockOperator_norm_le _ _ _ _

end CoarseAssembly

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

theorem map_rationalBoundaryUnitary (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    φ (rationalBoundaryUnitary F hF : A) =
      (rationalBoundaryUnitary (φ F) (hF.map φ) : B) := by
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul, map_neg, map_mul,
    map_cayleyUnitary]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyUnitization
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational boundary under a nonunital spatial homomorphism

The lift `1 + (F - 1)` in a unitization makes the complementary summand
explicit. This is the algebraic input to naturality under isometric spatial
inclusions, which extend an operator by the identity off its image.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem rationalBoundaryUnitary_identity_scalar (F : A) (hF : IsSelfAdjoint F) :
    (rationalBoundaryUnitary (identityUnitization F)
      (identityUnitization_selfAdjoint F hF) : Unitization ℂ A).fst = 1 := by
  have h := map_rationalBoundaryUnitary (unitizationScalar (A := A))
    (identityUnitization F) (identityUnitization_selfAdjoint F hF)
  have hsq : unitizationScalar (identityUnitization F) ^ 2 = (1 : ℂ) := by
    rw [unitizationScalar_identity]
    simp
  have hu := rationalBoundaryUnitary_eq_one _
    ((identityUnitization_selfAdjoint F hF).map (unitizationScalar (A := A))) hsq
  exact h.trans (congrArg (fun u : unitary ℂ => (u : ℂ)) hu)

theorem rationalBoundaryUnitary_identity_eval (F : A) (hF : IsSelfAdjoint F) :
    unitizationEval (rationalBoundaryUnitary (identityUnitization F)
      (identityUnitization_selfAdjoint F hF) : Unitization ℂ A) =
        (rationalBoundaryUnitary F hF : A) := by
  have h := map_rationalBoundaryUnitary (unitizationEval (A := A))
    (identityUnitization F) (identityUnitization_selfAdjoint F hF)
  simpa only [unitizationEval_identity] using h

theorem rationalBoundaryUnitary_identity (F : A) (hF : IsSelfAdjoint F) :
    (rationalBoundaryUnitary (identityUnitization F)
      (identityUnitization_selfAdjoint F hF) : Unitization ℂ A) =
        1 + (((rationalBoundaryUnitary F hF : A) - 1 : A) : Unitization ℂ A) := by
  have hs := rationalBoundaryUnitary_identity_scalar F hF
  have he := rationalBoundaryUnitary_identity_eval F hF
  rw [unitizationEval_apply, hs, map_one] at he
  apply Unitization.ext
  · simpa only [Unitization.fst_add, Unitization.fst_one, Unitization.fst_inr,
      add_zero] using hs
  · simpa only [Unitization.snd_add, Unitization.snd_one, Unitization.snd_inr,
      zero_add] using eq_sub_of_add_eq' he

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyNonunitalNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality for identity-extended nonunital homomorphisms -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem nonunital_rationalBoundaryUnitary (φ : A →⋆ₙₐ[ℂ] B)
    (F : A) (hF : IsSelfAdjoint F) :
    1 + φ ((rationalBoundaryUnitary F hF : A) - 1) =
      (rationalBoundaryUnitary (nonunitalIdentityExtension φ F)
        (nonunitalIdentityExtension_selfAdjoint φ F hF) : B) := by
  have h := map_rationalBoundaryUnitary (Unitization.starLift φ)
    (identityUnitization F) (identityUnitization_selfAdjoint F hF)
  rw [rationalBoundaryUnitary_identity F hF] at h
  simpa only [map_add, map_one, starLift_inr, starLift_identityUnitization] using h

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RepresentedIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
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

theorem unitaryExtension_star (c : OddCycle A) (u : A) :
    star (unitaryExtension c u) = unitaryExtension c (star u) := by
  rw [unitaryExtension, star_add, star_sub, star_one, ← map_star, ← map_star, star_one]
  rfl

theorem unitaryExtension_mul (c : OddCycle A) (u v : A) :
    unitaryExtension c u * unitaryExtension c v = unitaryExtension c (u * v) := by
  simp only [unitaryExtension, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    ← map_mul, one_mul, mul_one]
  abel

theorem unitaryExtension_unitary (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    star (unitaryExtension c u) * unitaryExtension c u = 1 ∧
      unitaryExtension c u * star (unitaryExtension c u) = 1 := by
  rw [unitaryExtension_star, unitaryExtension_mul, unitaryExtension_mul, hul, hur]
  constructor <;> simp only [unitaryExtension, add_sub_cancel]

theorem unitaryExtension_commutator (c : OddCycle A) (u : A)
    (hcomm : Commute c.operator (c.representation 1)) :
    c.operator * unitaryExtension c u - unitaryExtension c u * c.operator =
      c.operator * c.representation u - c.representation u * c.operator := by
  simp only [unitaryExtension, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [hcomm.eq]
  abel

def representedToeplitz (c : OddCycle A) (u : A) : End c.space :=
  toeplitzCompression (positiveProjection c.operator) (unitaryExtension c u)

def representedIndex (c : OddCycle A) (u : A) : ℤ :=
  (representedToeplitz c u).toLinearMap.index

theorem representedIndex_degenerate (c : OddCycle A) (u : A) (hd : c.Degenerate)
    (hself : IsSelfAdjoint c.operator) (hsq : c.operator * c.operator = 1)
    (hul : star u * u = 1) (hur : u * star u = 1) : representedIndex c u = 0 := by
  have hcomm : Commute c.operator (c.representation 1) := sub_eq_zero.mp (hd.1 1)
  have hc : Commute (positiveProjection c.operator) (unitaryExtension c u) := by
    apply sub_eq_zero.mp
    rw [positiveProjection_commutator, unitaryExtension_commutator c u hcomm, hd.1 u, smul_zero]
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c u hul hur
  obtain ⟨hl, hr⟩ := toeplitzCompression_unitary _ _ (positiveProjection_selfAdjoint _ hself)
    (positiveProjection_sq _ hsq) hUl hUr hc
  have hinv : (representedToeplitz c u).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (g := star (representedToeplitz c u)) hr hl
  exact LinearMap.index_of_bijective hinv.bijective

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RawCycleIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
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

theorem rawCycleToeplitz_compact_defects (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    IsCompactOperator (star (rawCycleToeplitz c u) * rawCycleToeplitz c u - 1 : End c.space) ∧
      IsCompactOperator (rawCycleToeplitz c u * star (rawCycleToeplitz c u) - 1 : End c.space) := by
  generalize hT : rawCycleToeplitz c u = T
  let F : End c.space := symmetricCutDown (c.representation 1) c.operator
  have hF : IsSelfAdjoint F := symmetricCutDown_selfAdjoint _ _ (representation_unit_selfAdjoint c)
  have hFP : Commute F (c.representation 1) :=
    commute_of_complement F _ hF (representation_unit_selfAdjoint c)
      (symmetricCutDown_complement _ _ (representation_unit_selfAdjoint c) (representation_unit_sq c))
  have hc : IsCompactOperator (F * c.representation u - c.representation u * F : End c.space) := by
    have h := c.cutDown.commutator_compact u
    change IsCompactOperator ((c.operator + representedCorrection c) * c.representation u -
      c.representation u * (c.operator + representedCorrection c) : End c.space) at h
    have he : c.operator + representedCorrection c = F := by unfold representedCorrection; dsimp [F]; abel
    rwa [he] at h
  have hU : IsCompactOperator (F * unitaryExtension c u - unitaryExtension c u * F : End c.space) := by
    have he : F * unitaryExtension c u - unitaryExtension c u * F =
        F * c.representation u - c.representation u * F := by
      simp only [unitaryExtension, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
      rw [hFP.eq]
      abel
    rw [he]
    exact hc
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c u hul hur
  have hFF : IsCompactOperator (F * F - 1 : End c.space) := symmetricCutDown_square_compact c
  have result := essentialToeplitz_compact_defects (H := c.space) F (unitaryExtension c u)
    hF hFF hUl hUr hU
  change toeplitzCompression (positiveProjection F) (unitaryExtension c u) = T at hT
  rw [hT] at result
  exact result


theorem rawCycleToeplitz_fredholm (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) : (rawCycleToeplitz c u).IsFredholm := by
  obtain ⟨hl, hr⟩ := rawCycleToeplitz_compact_defects c u hul hur
  exact isFredholm_of_compact_essential_unitary _ hl hr

theorem rawCycleIndex_homotopy (h : OddHomotopy A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    rawCycleIndex (h.eval start) u = rawCycleIndex (h.eval finish) u := by
  apply fredholmIndex_homotopy (fun t => rawCycleToeplitz (h.eval t) u)
  · have hP := h.continuous_representation (1 : A)
    have hB := (hP.mul h.continuous_operator).mul hP
    have hF : Continuous (fun t => symmetricCutDown (h.representation t 1) (h.operator t)) :=
      ((hB.add hB.star).const_smul (1 / 2 : ℝ)).add (continuous_const.sub hP)
    have hpos : Continuous (fun t => positiveProjection
        (symmetricCutDown (h.representation t 1) (h.operator t))) :=
      (hF.add continuous_const).const_smul (1 / 2 : ℝ)
    have hU : Continuous (fun t => h.representation t u + (1 - h.representation t 1)) :=
      (h.continuous_representation u).add (continuous_const.sub hP)
    change Continuous (fun t => positiveProjection
      (symmetricCutDown (h.representation t 1) (h.operator t)) *
      (h.representation t u + (1 - h.representation t 1)) *
      positiveProjection (symmetricCutDown (h.representation t 1) (h.operator t)) +
      (1 - positiveProjection (symmetricCutDown (h.representation t 1) (h.operator t))))
    exact ((hpos.mul hU).mul hpos).add (continuous_const.sub hpos)
  · intro t
    exact rawCycleToeplitz_fredholm (h.eval t) u hul hur

variable {B : Type} [CStarAlgebra B]

theorem rawCycleIndex_precomp (c : OddCycle A) (φ : B →⋆ₙₐ[ℂ] A)
    (hφ : φ 1 = 1) (u : B) : rawCycleIndex (c.precomp φ) u = rawCycleIndex c (φ u) := by
  have he : rawCycleToeplitz (c.precomp φ) u = rawCycleToeplitz c (φ u) := by
    change toeplitzCompression (positiveProjection (symmetricCutDown
      (c.representation (φ 1)) c.operator))
      (c.representation (φ u) + (1 - c.representation (φ 1))) = _
    rw [hφ]
    rfl
  exact congrArg (fun T : End c.space => T.toLinearMap.index) he

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DegenerateCutDown
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degenerate cycles have zero explicit Toeplitz index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem rawCycleToeplitz_eq_cutDown (c : OddCycle A) (u : A) :
    rawCycleToeplitz c u = representedToeplitz c.cutDown u := by
  change toeplitzCompression (positiveProjection (symmetricCutDown (c.representation 1) c.operator))
    (unitaryExtension c u) = toeplitzCompression
      (positiveProjection (c.operator + representedCorrection c)) (unitaryExtension c u)
  have he : c.operator + representedCorrection c = symmetricCutDown (c.representation 1) c.operator := by
    unfold representedCorrection
    abel
  rw [he]

theorem rawCycleIndex_degenerate (c : OddCycle A) (u : A) (hd : c.Degenerate)
    (hul : star u * u = 1) (hur : u * star u = 1) : rawCycleIndex c u = 0 := by
  have hi := representedIndex_degenerate c.cutDown u (cutDown_degenerate c hd)
    (cutDown_selfAdjoint c) (cutDown_degenerate_sq c hd) hul hur
  have he : rawCycleIndex c u = representedIndex c.cutDown u :=
    congrArg (fun T : End c.space => T.toLinearMap.index) (rawCycleToeplitz_eq_cutDown c u)
  exact he.trans hi

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UnitaryIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unitary invariance of the explicit cycle index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

variable {A : Type} [CStarAlgebra A]

theorem rawCycleToeplitz_unitary (c d : OddCycle A) (h : c.UnitaryEquivalent d) (u : A) :
    rawCycleToeplitz d u = h.unitary.conjStarAlgEquiv (rawCycleToeplitz c u) := by
  let φ : End c.space →⋆ₐ[ℂ] End d.space := h.unitary.conjStarAlgEquiv.toStarAlgHom
  have hrep (a : A) : d.representation a = φ (c.representation a) :=
    (h.representation_eq a).trans (operatorConjugation_equiv h.unitary _)
  have hop : d.operator = φ c.operator :=
    h.operator_eq.trans (operatorConjugation_equiv h.unitary _)
  change rawCycleToeplitz d u = φ (rawCycleToeplitz c u)
  unfold rawCycleToeplitz
  rw [toeplitzCompression_map φ, positiveProjection_map φ, symmetricCutDown_map φ]
  simp only [unitaryExtension, map_add, map_sub, map_one]
  rw [hop, hrep 1, hrep u]

theorem rawCycleIndex_unitary (c d : OddCycle A) (h : c.UnitaryEquivalent d) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) : rawCycleIndex d u = rawCycleIndex c u := by
  unfold rawCycleIndex
  rw [rawCycleToeplitz_unitary c d h u]
  exact fredholmIndex_conjugation h.unitary _ (rawCycleToeplitz_fredholm c u hul hur)

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

theorem rawCycleToeplitz_directSum (h : c.IsDirectSum d e) (u : A) :
    h.block (rawCycleToeplitz c u) (rawCycleToeplitz d u) = rawCycleToeplitz e u := by
  unfold rawCycleToeplitz
  have hr : h.block (c.representation 1) (d.representation 1) = e.representation 1 :=
    (h.representation_eq 1).symm
  have ho : h.block c.operator d.operator = e.operator := h.operator_eq.symm
  rw [h.block_toeplitz, h.block_positive, h.block_cutDown, hr, ho, h.block_unitaryExtension]

theorem rawCycleIndex_directSum (h : c.IsDirectSum d e) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    rawCycleIndex e u = rawCycleIndex c u + rawCycleIndex d u := by
  have hc := rawCycleToeplitz_fredholm c u hul hur
  have hd := rawCycleToeplitz_fredholm d u hul hur
  have he := rawCycleToeplitz_fredholm e u hul hur
  have hcoord : h.coordinates.IsFredholm := h.coordinateEquiv.isFredholm
  have hincl : h.inclusion.IsFredholm := h.coordinateEquiv.symm.isFredholm
  have hcz : h.coordinates.toLinearMap.index = 0 :=
    LinearMap.index_of_bijective h.coordinateEquiv.bijective
  have hiz : h.inclusion.toLinearMap.index = 0 :=
    LinearMap.index_of_bijective h.coordinateEquiv.symm.bijective
  have hi : (h.coordinates ∘L rawCycleToeplitz e u ∘L h.inclusion).toLinearMap.index =
      (rawCycleToeplitz e u).toLinearMap.index := by
    rw [hcoord.index_comp (he.comp hincl), he.index_comp hincl, hcz, hiz, zero_add, add_zero]
  have hprod : h.coordinates ∘L rawCycleToeplitz e u ∘L h.inclusion =
      (rawCycleToeplitz c u).prodMap (rawCycleToeplitz d u) := by
    rw [← rawCycleToeplitz_directSum h u, h.block_coordinates]
  rw [hprod] at hi
  exact hi.symm.trans (fredholmIndex_prodMap _ _ hc hd)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_IndexPairing
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.homotopySlice_finish _root_.OAI.CoarseAssembly.Analytic.homotopySlice_start _root_.OAI.CoarseAssembly.Analytic.intervalGrid_finish _root_.OAI.CoarseAssembly.Analytic.intervalGrid_start _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_finish _root_.OAI.CoarseAssembly.Analytic.involutionUnitaryPath_start _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_finish _root_.OAI.CoarseAssembly.Analytic.partialIsometryDilationPath_start _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_finish _root_.OAI.CoarseAssembly.Analytic.projectionSignPath_start _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_finish _root_.OAI.CoarseAssembly.Analytic.semicircleUnitary_start _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar-unitary index pairing on odd analytic K-homology

All four defining Fredholm-cycle relations are respected by the explicit
Toeplitz index. Hence it descends to the existing quotient group.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def indexFree (u : A) : FreeAbelianGroup (OddCycle A) →+ ℤ :=
  FreeAbelianGroup.lift (fun c => rawCycleIndex c u)

theorem indexFree_relation (u : A) (hul : star u * u = 1) (hur : u * star u = 1)
    {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) : indexFree u z = 0 := by
  cases hz with
  | degenerate c h =>
    simpa [indexFree] using rawCycleIndex_degenerate c u h hul hur
  | unitary c d h =>
    simpa [indexFree] using sub_eq_zero.mpr (rawCycleIndex_unitary c d h u hul hur).symm
  | directSum c d e h =>
    simpa [indexFree] using sub_eq_zero.mpr (rawCycleIndex_directSum h u hul hur)
  | homotopy h =>
    simpa [indexFree] using sub_eq_zero.mpr (rawCycleIndex_homotopy h u hul hur)

/-- Pairing an odd analytic class with an actual scalar unitary. -/
def indexPairing (u : A) (hul : star u * u = 1) (hur : u * star u = 1) : OddK A →+ ℤ :=
  QuotientAddGroup.lift (relations A) (indexFree u)
    ((AddSubgroup.closure_le _).2 (fun _ hz => indexFree_relation u hul hur hz))

@[simp] theorem indexPairing_cycleClass (u : A) (hul : star u * u = 1)
    (hur : u * star u = 1) (c : OddCycle A) :
    indexPairing u hul hur (cycleClass A c) = rawCycleIndex c u :=
  FreeAbelianGroup.lift_apply_of _ _

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactIndexPairing
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar-unitary pairing for compact spaces -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y]

/-- The index pairing on the actual locally finite K-homology group. -/
def compactIndexPairing (f : C(X, Circle)) : LocallyFiniteK1 X →+ ℤ :=
  (indexPairing (compactUnitary f) (compactUnitary_star_mul f)
    (compactUnitary_mul_star f)).comp (precomp compactFunctionLift)

@[simp] theorem compactIndexPairing_cycleClass (f : C(X, Circle)) (c : OddCycle C₀(X, ℂ)) :
    compactIndexPairing f (cycleClass C₀(X, ℂ) c) =
      rawCycleIndex (c.precomp compactFunctionLift) (compactUnitary f) := by
  simp only [compactIndexPairing, AddMonoidHom.comp_apply, precomp_cycleClass,
    indexPairing_cycleClass]

theorem compactFunctionLift_pullback (γ : C(X, Y)) :
    (pullback (compactMap γ)).comp (compactFunctionLift (X := Y)) =
      (compactFunctionLift (X := X)).comp
        (ContinuousMap.compStarAlgHom' ℂ ℂ γ).toNonUnitalStarAlgHom := by
  ext a x
  rfl

theorem compactIndexPairing_natural (f : C(Y, Circle)) (γ : C(X, Y)) :
    (compactIndexPairing f).comp (pushforward (compactMap γ)) =
      compactIndexPairing (f.comp γ) := by
  apply hom_ext
  intro c
  simp only [AddMonoidHom.comp_apply, pushforward, precomp_cycleClass,
    compactIndexPairing_cycleClass, OddCycle.precomp_comp, compactFunctionLift_pullback]
  let φ := (ContinuousMap.compStarAlgHom' ℂ ℂ γ).toNonUnitalStarAlgHom
  have hφ : φ 1 = 1 := map_one (ContinuousMap.compStarAlgHom' ℂ ℂ γ)
  exact rawCycleIndex_precomp (c.precomp compactFunctionLift) φ hφ (compactUnitary f)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UnitaryHomotopyIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homotopy invariance in the unitary argument of the index pairing -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

variable {A : Type} [CStarAlgebra A]

theorem rawCycleIndex_unitaryHomotopy (c : OddCycle A) (u : Interval → A)
    (hu : Continuous u) (hul : ∀ t, star (u t) * u t = 1)
    (hur : ∀ t, u t * star (u t) = 1) :
    rawCycleIndex c (u start) = rawCycleIndex c (u finish) := by
  apply fredholmIndex_homotopy (fun t => rawCycleToeplitz c (u t))
  · have hrep : Continuous (fun t => c.representation (u t)) := (map_continuous c.representation).comp hu
    have hext : Continuous (fun t => unitaryExtension c (u t)) := hrep.add continuous_const
    exact ((continuous_const.mul hext).mul continuous_const).add continuous_const
  · intro t
    exact rawCycleToeplitz_fredholm c (u t) (hul t) (hur t)

theorem indexPairing_unitaryHomotopy (u : Interval → A) (hu : Continuous u)
    (hul : ∀ t, star (u t) * u t = 1) (hur : ∀ t, u t * star (u t) = 1) :
    indexPairing (u start) (hul start) (hur start) =
      indexPairing (u finish) (hul finish) (hur finish) := by
  apply hom_ext
  intro c
  simp only [indexPairing_cycleClass]
  exact rawCycleIndex_unitaryHomotopy c u hu hul hur

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

theorem compactIndexPairing_homotopy {f g : C(X, Circle)} (F : f.Homotopy g) :
    compactIndexPairing f = compactIndexPairing g := by
  let u : Interval → C(X, ℂ) := fun t => compactUnitary (homotopySlice F t)
  have hu : Continuous u := by
    let coeCircle : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩
    exact (ContinuousMap.continuous_postcomp coeCircle).comp F.toContinuousMap.curry.continuous
  have hul (t : Interval) : star (u t) * u t = 1 := compactUnitary_star_mul _
  have hur (t : Interval) : u t * star (u t) = 1 := compactUnitary_mul_star _
  have hi := indexPairing_unitaryHomotopy u hu hul hur
  have he : indexPairing (compactUnitary f) (compactUnitary_star_mul f)
      (compactUnitary_mul_star f) = indexPairing (compactUnitary g)
      (compactUnitary_star_mul g) (compactUnitary_mul_star g) := by
    simpa only [u, homotopySlice_start, homotopySlice_finish] using hi
  unfold compactIndexPairing
  rw [he]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_MultiplicativeIndexPairing
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity of the scalar-unitary pairing under multiplication -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem rawCycleIndex_mul (c : OddCycle A) (u v : A)
    (hul : star u * u = 1) (hur : u * star u = 1)
    (hvl : star v * v = 1) (hvr : v * star v = 1) :
    rawCycleIndex c (u * v) = rawCycleIndex c u + rawCycleIndex c v := by
  have hc : Commute c.cutDown.operator (c.cutDown.representation 1) :=
    commute_of_complement _ _ (cutDown_selfAdjoint c)
      (representation_unit_selfAdjoint c.cutDown) (cutDown_complement c)
  have hcomm (a : A) : IsCompactOperator
      (c.cutDown.operator * unitaryExtension c.cutDown a -
        unitaryExtension c.cutDown a * c.cutDown.operator : End c.cutDown.space) := by
    rw [unitaryExtension_commutator c.cutDown a hc]
    exact c.cutDown.commutator_compact a
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c.cutDown u hul hur
  obtain ⟨hVl, hVr⟩ := unitaryExtension_unitary c.cutDown v hvl hvr
  have hi := essentialToeplitz_index_mul c.cutDown.operator
    (unitaryExtension c.cutDown u) (unitaryExtension c.cutDown v)
    (cutDown_selfAdjoint c) (cutDown_square_compact c) hUl hUr hVl hVr (hcomm u) (hcomm v)
  rw [unitaryExtension_mul] at hi
  simp only [rawCycleIndex, rawCycleToeplitz_eq_cutDown, representedToeplitz]
  exact hi

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

theorem compactIndexPairing_mul (f g : C(X, Circle)) :
    compactIndexPairing (f * g) = compactIndexPairing f + compactIndexPairing g := by
  apply hom_ext
  intro c
  simp only [AddMonoidHom.add_apply, compactIndexPairing_cycleClass]
  have he : compactUnitary (f * g) = compactUnitary f * compactUnitary g := rfl
  rw [he]
  exact rawCycleIndex_mul _ _ _ (compactUnitary_star_mul f) (compactUnitary_mul_star f)
    (compactUnitary_star_mul g) (compactUnitary_mul_star g)

theorem compactIndexPairing_one : compactIndexPairing (1 : C(X, Circle)) = 0 := by
  have h := compactIndexPairing_mul (1 : C(X, Circle)) 1
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

theorem compactIndexPairing_pow (f : C(X, Circle)) (n : ℕ) :
    compactIndexPairing (f ^ n) = n • compactIndexPairing f := by
  induction n with
  | zero => simp only [pow_zero, compactIndexPairing_one, zero_smul]
  | succ n ih => rw [pow_succ, compactIndexPairing_mul, ih, succ_nsmul]

theorem compactIndexPairing_inv (f : C(X, Circle)) :
    compactIndexPairing f⁻¹ = -compactIndexPairing f := by
  have h := compactIndexPairing_mul f f⁻¹
  rw [mul_inv_cancel, compactIndexPairing_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem compactIndexPairing_zpow (f : C(X, Circle)) (n : ℤ) :
    compactIndexPairing (f ^ n) = n • compactIndexPairing f := by
  cases n with
  | ofNat n => simpa using compactIndexPairing_pow f n
  | negSucc n =>
    rw [zpow_negSucc, compactIndexPairing_inv, compactIndexPairing_pow]
    simp only [Int.negSucc_eq, neg_smul]
    rw [← Nat.cast_add_one, natCast_zsmul]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NegativeProjection
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative-frequency projection for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

theorem negativeProjection_sq : negativeProjection * negativeProjection = negativeProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change negativeProjection (negativeProjection x) n = negativeProjection x n
  rw [negativeProjection_apply (negativeProjection x) n, negativeProjection_apply x n]
  split_ifs <;> rfl

theorem negativeProjection_selfAdjoint : IsSelfAdjoint negativeProjection := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ (negativeProjection x n) (y n) = inner ℂ (x n) (negativeProjection y n)
  rw [negativeProjection_apply x n, negativeProjection_apply y n]
  split_ifs <;> simp

/-- The projection/shift commutator has exactly one nonzero row. -/
theorem negativeProjection_commutator (x : CircleSequence) :
    (negativeProjection * bilateralShift - bilateralShift * negativeProjection) x =
      -lp.single 2 0 (x (-1)) := by
  apply lp.ext
  funext n
  change negativeProjection (bilateralShift x) n - bilateralShift (negativeProjection x) n = _
  rw [negativeProjection_apply (bilateralShift x) n, bilateralShift_apply (negativeProjection x) n,
    negativeProjection_apply x (n - 1)]
  simp only [lp.coeFn_neg, Pi.neg_apply, lp.single_apply, Pi.single_apply]
  simp only [bilateralShift_apply x n]
  by_cases hzero : n = 0
  · subst n
    norm_num
  · have hsign : n - 1 < 0 ↔ n < 0 := by omega
    simp [hsign, hzero]


theorem negativeProjection_commutator_compact : IsCompactOperator
    (negativeProjection * bilateralShift - bilateralShift * negativeProjection) := by
  let ev : CircleSequence →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-1)
  let ins : ℂ →L[ℂ] CircleSequence := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0
  have he : negativeProjection * bilateralShift - bilateralShift * negativeProjection =
      -(ins ∘L ev) := by
    apply ContinuousLinearMap.ext
    intro x
    exact negativeProjection_commutator x
  rw [he]
  exact ((isCompactOperator_of_locallyCompactSpace_dom ev).clm_comp ins).neg

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleSequenceRepresentation
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous circle functions represented by the bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

/-- Continuous functional calculus of the actual bilateral shift. -/
def circleRepresentation : C(Circle, ℂ) →⋆ₐ[ℂ] End circleSequenceSpace :=
  cfcHomSuperset (isStarNormal_of_mem_unitary bilateralShift_mem_unitary) bilateralShift_spectrum_circle

@[simp] theorem circleRepresentation_coordinate : circleRepresentation circleCoordinate = bilateralShift :=
  cfcHomSuperset_id _ _

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_EssentialCommutant
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending compact commutators from the circle coordinate to every function -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

variable {H : HilbertSpace}

theorem compact_commutator_add (P T S : End H)
    (hT : IsCompactOperator (P * T - T * P : End H))
    (hS : IsCompactOperator (P * S - S * P : End H)) :
    IsCompactOperator (P * (T + S) - (T + S) * P : End H) := by
  have he : P * (T + S) - (T + S) * P = (P * T - T * P) + (P * S - S * P) := by noncomm_ring
  rw [he]
  exact hT.add hS

/-- Operators commuting with `P` modulo compacts, together with their adjoints. -/
def compactCommutant (P : End H) : StarSubalgebra ℂ (End H) where
  carrier := {T | IsCompactOperator (P * T - T * P : End H) ∧
    IsCompactOperator (P * star T - star T * P : End H)}
  zero_mem' := by
    change IsCompactOperator (P * 0 - 0 * P : End H) ∧ IsCompactOperator (P * star 0 - star 0 * P : End H)
    simp only [star_zero, mul_zero, zero_mul, sub_self]
    exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  one_mem' := by
    change IsCompactOperator (P * 1 - 1 * P : End H) ∧ IsCompactOperator (P * star 1 - star 1 * P : End H)
    simp only [star_one, mul_one, one_mul, sub_self]
    exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  add_mem' hT hS := by
    refine ⟨compact_commutator_add P _ _ hT.1 hS.1, ?_⟩
    rw [star_add]
    exact compact_commutator_add P _ _ hT.2 hS.2
  mul_mem' hT hS := by
    refine ⟨compact_commutator_mul P _ _ hT.1 hS.1, ?_⟩
    rw [star_mul]
    exact compact_commutator_mul P _ _ hS.2 hT.2
  algebraMap_mem' z := by
    have hz (z : ℂ) : P * algebraMap ℂ (End H) z - algebraMap ℂ (End H) z * P = 0 :=
      sub_eq_zero.mpr (Algebra.commutes z P).symm
    change IsCompactOperator (P * algebraMap ℂ (End H) z - algebraMap ℂ (End H) z * P) ∧
      IsCompactOperator (P * star (algebraMap ℂ (End H) z) - star (algebraMap ℂ (End H) z) * P)
    have hs : star (algebraMap ℂ (End H) z) = algebraMap ℂ (End H) (star z) := by
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    rw [hz, hs, hz]
    exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  star_mem' {T} hT := by
    change IsCompactOperator (P * star T - star T * P) ∧
      IsCompactOperator (P * star (star T) - star (star T) * P)
    exact ⟨hT.2, by simpa only [star_star] using hT.1⟩

theorem compactCommutant_closed (P : End H) : IsClosed (compactCommutant P : Set (End H)) := by
  change IsClosed ({T : End H | IsCompactOperator (P * T - T * P)} ∩
    {T : End H | IsCompactOperator (P * star T - star T * P)})
  exact (isClosed_setOfPred_isCompactOperator.preimage
    ((continuous_const.mul continuous_id).sub (continuous_id.mul continuous_const))).inter
      (isClosed_setOfPred_isCompactOperator.preimage
        ((continuous_const.mul continuous_star).sub (continuous_star.mul continuous_const)))

theorem circleRepresentation_commutator (f : C(Circle, ℂ)) : IsCompactOperator
    (negativeProjection * circleRepresentation f - circleRepresentation f * negativeProjection) := by
  let S : StarSubalgebra ℂ C(Circle, ℂ) :=
    (compactCommutant negativeProjection).comap circleRepresentation
  have hcoord : circleCoordinate ∈ S := by
    change IsCompactOperator (negativeProjection * circleRepresentation circleCoordinate -
      circleRepresentation circleCoordinate * negativeProjection) ∧
      IsCompactOperator (negativeProjection * star (circleRepresentation circleCoordinate) -
      star (circleRepresentation circleCoordinate) * negativeProjection)
    rw [circleRepresentation_coordinate]
    exact ⟨negativeProjection_commutator_compact,
      compact_commutator_star_unitary _ _ bilateralShift_unitary.1 bilateralShift_unitary.2
        negativeProjection_commutator_compact⟩
  have hsep : S.SeparatesPoints := by
    intro x y hxy
    exact ⟨circleCoordinate, ⟨circleCoordinate, hcoord, rfl⟩, fun he => hxy (Circle.coe_injective he)⟩
  have htop : S.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  have hclosed : IsClosed (S : Set C(Circle, ℂ)) :=
    (compactCommutant_closed negativeProjection).preimage (map_continuous circleRepresentation)
  have hle : S.topologicalClosure ≤ S := StarSubalgebra.topologicalClosure_minimal le_rfl hclosed
  rw [htop] at hle
  have hf : f ∈ S := hle (by trivial)
  exact hf.1

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ShiftIndex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.summandIsometry_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The index-one compressed bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

def shiftToeplitz : End circleSequenceSpace := toeplitzCompression negativeProjection bilateralShift

def shiftToeplitzInverse : End circleSequenceSpace := toeplitzCompression negativeProjection (star bilateralShift)

theorem shiftToeplitz_apply (x : CircleSequence) (n : ℤ) :
    shiftToeplitz x n = if n < 0 then x (n - 1) else x n := by
  change negativeProjection (bilateralShift (negativeProjection x)) n +
    (x n - negativeProjection x n) = _
  rw [negativeProjection_apply (bilateralShift (negativeProjection x)) n,
    bilateralShift_apply (negativeProjection x) n,
    negativeProjection_apply x (n - 1), negativeProjection_apply x n]
  split_ifs <;> simp_all
  all_goals omega

theorem shiftToeplitzInverse_apply (x : CircleSequence) (n : ℤ) :
    shiftToeplitzInverse x n = if n < 0 then (if n + 1 < 0 then x (n + 1) else 0) else x n := by
  change negativeProjection (star bilateralShift (negativeProjection x)) n +
    (x n - negativeProjection x n) = _
  rw [negativeProjection_apply (star bilateralShift (negativeProjection x)) n,
    bilateralShift_star_apply (negativeProjection x) n,
    negativeProjection_apply x (n + 1), negativeProjection_apply x n]
  split_ifs <;> simp_all

theorem shiftToeplitz_right_inverse : shiftToeplitz * shiftToeplitzInverse = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change shiftToeplitz (shiftToeplitzInverse x) n = x n
  rw [shiftToeplitz_apply (shiftToeplitzInverse x) n]
  by_cases hn : n < 0
  · rw [ite_eq_left hn, shiftToeplitzInverse_apply x (n - 1),
      ite_eq_left (by omega : n - 1 < 0), ite_eq_left (by omega : n - 1 + 1 < 0)]
    rw [sub_add_cancel]
  · rw [ite_eq_right hn, shiftToeplitzInverse_apply x n, ite_eq_right hn]

theorem shiftToeplitz_surjective : Function.Surjective shiftToeplitz := by
  intro x
  refine ⟨shiftToeplitzInverse x, ?_⟩
  exact DFunLike.congr_fun shiftToeplitz_right_inverse x

/-- The kernel is exactly the last negative Fourier coordinate. -/
theorem shiftToeplitz_ker : shiftToeplitz.ker =
    Submodule.span ℂ {lp.single 2 (-1 : ℤ) (1 : ℂ)} := by
  apply le_antisymm
  · intro x hx
    have hz : shiftToeplitz x = 0 := hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x (-1), ?_⟩
    apply lp.ext
    funext n
    by_cases hn : n = -1
    · subst n
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self, smul_eq_mul, mul_one]
    · have hx0 : x n = 0 := by
        by_cases hneg : n < 0
        · have hnn : n + 1 < 0 := by omega
          have h := congrArg (fun y : CircleSequence => y (n + 1)) hz
          rw [shiftToeplitz_apply x (n + 1), ite_eq_left hnn] at h
          simpa only [add_sub_cancel_right, lp.coeFn_zero, Pi.zero_apply] using h
        · have h := congrArg (fun y : CircleSequence => y n) hz
          rw [shiftToeplitz_apply x n, ite_eq_right hneg] at h
          exact h
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 (-1 : ℤ) (1 : ℂ) hn,
        smul_zero, hx0]
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change shiftToeplitz (lp.single 2 (-1 : ℤ) (1 : ℂ)) = 0
    apply lp.ext
    funext n
    rw [shiftToeplitz_apply]
    split_ifs with hn
    · exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 (-1 : ℤ) (1 : ℂ) (by omega)
    · exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 (-1 : ℤ) (1 : ℂ) (by omega)

theorem shiftToeplitz_index : shiftToeplitz.toLinearMap.index = 1 := by
  have he : (lp.single 2 (-1 : ℤ) (1 : ℂ) : CircleSequence) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : CircleSequence => x (-1)) h
    have hzero : (1 : ℂ) = 0 := by
      simpa only [lp.single_apply_self, lp.coeFn_zero, Pi.zero_apply] using h'
    exact one_ne_zero hzero
  rw [LinearMap.index_eq_finrank_sub, shiftToeplitz_ker,
    LinearMap.range_eq_top.mpr shiftToeplitz_surjective]
  simp only [finrank_span_singleton he, Module.finrank_zero_of_subsingleton, Nat.cast_one,
    Nat.cast_zero, sub_zero]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NegativeCircleCycle
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit circle Fredholm cycle and its coordinate index -/

noncomputable section

namespace CoarseAssembly.Analytic

def negativeCircleOperator : End circleSequenceSpace := negativeProjection + negativeProjection - 1

theorem negativeCircleOperator_selfAdjoint : IsSelfAdjoint negativeCircleOperator := by
  change star (negativeProjection + negativeProjection - 1) = _
  rw [star_sub, star_add, negativeProjection_selfAdjoint.star_eq, star_one]
  rfl

theorem negativeCircleOperator_sq : negativeCircleOperator * negativeCircleOperator = 1 := by
  unfold negativeCircleOperator
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, negativeProjection_sq]
  abel

theorem negativeCircleOperator_commutator (f : C(Circle, ℂ)) : IsCompactOperator
    (negativeCircleOperator * circleRepresentation f - circleRepresentation f * negativeCircleOperator) := by
  have he : negativeCircleOperator * circleRepresentation f - circleRepresentation f * negativeCircleOperator =
      (negativeProjection * circleRepresentation f - circleRepresentation f * negativeProjection) +
      (negativeProjection * circleRepresentation f - circleRepresentation f * negativeProjection) := by
    unfold negativeCircleOperator
    noncomm_ring
  rw [he]
  exact (circleRepresentation_commutator f).add (circleRepresentation_commutator f)

def negativeCircleCycle : OddCycle C(Circle, ℂ) where
  space := circleSequenceSpace
  representation := circleRepresentation.toNonUnitalStarAlgHom
  operator := negativeCircleOperator
  commutator_compact := negativeCircleOperator_commutator
  square_compact f := by
    change IsCompactOperator ((negativeCircleOperator * negativeCircleOperator - 1) * circleRepresentation f : End circleSequenceSpace)
    rw [negativeCircleOperator_sq, sub_self, zero_mul]
    exact isCompactOperator_zero
  adjoint_compact f := by
    change IsCompactOperator ((star negativeCircleOperator - negativeCircleOperator) * circleRepresentation f : End circleSequenceSpace)
    rw [negativeCircleOperator_selfAdjoint.star_eq, sub_self, zero_mul]
    exact isCompactOperator_zero

theorem negativeCircleCycle_coordinate_index : rawCycleIndex negativeCircleCycle circleCoordinate = 1 := by
  have hcut : symmetricCutDown (circleRepresentation 1) negativeCircleOperator = negativeCircleOperator := by
    rw [map_one]
    unfold symmetricCutDown
    rw [one_mul, mul_one, negativeCircleOperator_selfAdjoint.star_eq]
    module
  have hpos : positiveProjection negativeCircleOperator = negativeProjection := by
    unfold positiveProjection negativeCircleOperator
    module
  have hunit : circleRepresentation circleCoordinate + (1 - circleRepresentation 1) = bilateralShift := by
    rw [circleRepresentation_coordinate, map_one, sub_self, add_zero]
  unfold rawCycleIndex
  change (toeplitzCompression (positiveProjection
    (symmetricCutDown (circleRepresentation 1) negativeCircleOperator))
    (circleRepresentation circleCoordinate + (1 - circleRepresentation 1))).toLinearMap.index = 1
  rw [hcut, hpos, hunit]
  exact shiftToeplitz_index

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CircleCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional circle class of coordinate index one -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

theorem compactFunctionForget_lift :
    (compactFunctionForget (X := X)).comp compactFunctionLift = NonUnitalStarAlgHom.id ℂ C(X, ℂ) := by
  ext f x
  rfl

def negativeCircleClass : LocallyFiniteK1 Circle :=
  cycleClass C₀(Circle, ℂ) (negativeCircleCycle.precomp compactFunctionForget)

theorem negativeCircleClass_coordinate_index :
    compactIndexPairing (ContinuousMap.id Circle) negativeCircleClass = 1 := by
  rw [negativeCircleClass, compactIndexPairing_cycleClass, OddCycle.precomp_comp,
    compactFunctionForget_lift, OddCycle.precomp_id]
  exact negativeCircleCycle_coordinate_index

end CoarseAssembly.Analytic

namespace CoarseAssembly

open Analytic

def circleFundamental : LocallyFiniteK1 WindingCircle :=
  pushforward (compactMap ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm : C(Circle, WindingCircle)))
    negativeCircleClass

open Congruence Rips

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactBlockSum
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.CoarseAssembly.baseUnionMetric
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

theorem blockSum_compact (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)
    (hc : ∀ j, IsCompactOperator (K j)) (htail : Tendsto (fun j => ‖K j‖) atTop (𝓝 0)) :
    IsCompactOperator (CoarseAssembly.blockOperator K C hC hK) := by
  apply isCompactOperator_of_tendsto (l := atTop) (F := fun N => truncatedBlockSum H K N C hC hK)
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (CoarseAssembly.blockOperator_dist_le _ _ C C (ε / 2) hC hC
      (by positivity) (truncateBlocks_norm H K n C hC hK) hK ?_) (by linarith)
    intro j
    unfold truncateBlocks
    split_ifs with hj
    · simp only [sub_self, norm_zero]
      positivity
    · simp only [zero_sub, norm_neg]
      have hjn : N ≤ j := hn.trans (Nat.le_of_not_gt hj)
      have hsmall := hN j hjn
      simpa only [dist_zero_right, norm_norm] using le_of_lt hsmall
  · exact Filter.Eventually.of_forall (truncatedBlockSum_compact H K C hC hK hc)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactFamilyHomotopy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
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

theorem compactFamilyPullback_continuous (F : ∀ j, C(Interval × X j, Y j))
    (f : C₀(Sigma Y, ℂ)) :
    Continuous (fun t => pullback (compactFamilySlice F t) f) := by
  have hlocal (j : ℕ) : Continuous (fun t : Interval =>
      (sigmaFunctionRestriction Y j f).comp ((F j).curry t)) :=
    (ContinuousMap.continuous_postcomp (sigmaFunctionRestriction Y j f)).comp
      (F j).curry.continuous
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (sigmaFunctionRestriction_norm_tendsto Y f) (ε / 4) (by positivity)
  have hhead : ∀ᶠ t in 𝓝 t₀, ∀ j ∈ Finset.range N,
      dist ((sigmaFunctionRestriction Y j f).comp ((F j).curry t))
        ((sigmaFunctionRestriction Y j f).comp ((F j).curry t₀)) < ε / 2 := by
    apply (Finset.eventually_all _).mpr
    intro j _
    exact Metric.tendsto_nhds.mp (hlocal j).continuousAt (ε / 2) (by positivity)
  filter_upwards [hhead] with t ht
  change dist (pullback (compactFamilySlice F t) f).toBCF
    (pullback (compactFamilySlice F t₀) f).toBCF < ε
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity : 0 ≤ ε / 2)).mpr ?_)
    (by linarith : ε / 2 < ε)
  rintro ⟨j, x⟩
  change dist (sigmaFunctionRestriction Y j f ((F j).curry t x))
    (sigmaFunctionRestriction Y j f ((F j).curry t₀ x)) ≤ ε / 2
  by_cases hj : j < N
  · exact (ContinuousMap.dist_apply_le_dist x).trans
      (ht j (Finset.mem_range.mpr hj)).le
  · have hb : ‖sigmaFunctionRestriction Y j f‖ < ε / 4 := by
      simpa only [dist_zero_right, norm_norm] using hN j (by omega)
    calc
      _ ≤ ‖sigmaFunctionRestriction Y j f ((F j).curry t x)‖ +
          ‖sigmaFunctionRestriction Y j f ((F j).curry t₀ x)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖sigmaFunctionRestriction Y j f‖ + ‖sigmaFunctionRestriction Y j f‖ :=
        add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
      _ ≤ ε / 2 := by linarith

def compactFamilyCycleHomotopy (F : ∀ j, C(Interval × X j, Y j))
    (c : OddCycle C₀(Sigma X, ℂ)) : OddHomotopy C₀(Sigma Y, ℂ) where
  space := c.space
  representation t := c.representation.comp (pullback (compactFamilySlice F t))
  operator _ := c.operator
  continuous_representation f :=
    (show Continuous (c.representation : C₀(Sigma X, ℂ) → End c.space) from
      map_continuous _).comp (compactFamilyPullback_continuous F f)
  continuous_operator := continuous_const
  commutator_compact t f := c.commutator_compact (pullback (compactFamilySlice F t) f)
  square_compact t f := c.square_compact (pullback (compactFamilySlice F t) f)
  adjoint_compact t f := c.adjoint_compact (pullback (compactFamilySlice F t) f)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteCycleSum
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
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

theorem diagonal_compact_of_zero_tail (H : ℕ → HilbertSpace) (K : ∀ j, End (H j))
    (T : End (countableHilbertSpace H)) (N : ℕ)
    (hT : ∀ x j, (T x) j = K j (x j))
    (hK : ∀ j, IsCompactOperator (K j)) (hzero : ∀ j, N ≤ j → K j = 0) :
    IsCompactOperator T := by
  let C := ∑ j ∈ Finset.range N, ‖K j‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => norm_nonneg (K j))
  have hb : ∀ j, ‖K j‖ ≤ C := by
    intro j
    by_cases hj : j < N
    · exact Finset.single_le_sum (fun k _ => norm_nonneg (K k)) (Finset.mem_range.mpr hj)
    · rw [hzero j (Nat.le_of_not_gt hj), norm_zero]
      exact hC
  have he : T = truncatedBlockSum H K N C hC hb := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    rw [hT, truncatedBlockSum_apply]
    by_cases hj : j < N
    · simp only [hj, ite_true, if_true]
    · simp only [hj, ite_false, if_false, hzero j (Nat.le_of_not_gt hj), zero_apply]
  rw [he]
  exact truncatedBlockSum_compact H K C hC hb hK N

variable {A : Type} [CStarAlgebra A]

def finiteActiveCycle (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate) : OddCycle A where
  space := countableHilbertSpace (familyHilbert c)
  representation := familyRepresentation c
  operator := blockOperator (fun j => (c j).operator) C hC hnorm
  commutator_compact a := by
    apply diagonal_compact_of_zero_tail (familyHilbert c)
      (fun j => (c j).operator * (c j).representation a - (c j).representation a * (c j).operator)
      _ N
    · intro x j
      rfl
    · exact fun j => (c j).commutator_compact a
    · exact fun j hj => (htail j hj).1 a
  square_compact a := by
    apply diagonal_compact_of_zero_tail (familyHilbert c)
      (fun j => ((c j).operator * (c j).operator - 1) * (c j).representation a) _ N
    · intro x j
      rfl
    · exact fun j => (c j).square_compact a
    · exact fun j hj => (htail j hj).2.1 a
  adjoint_compact a := by
    change IsCompactOperator
      (((blockOperator (fun j => (c j).operator) C hC hnorm).adjoint -
        blockOperator (fun j => (c j).operator) C hC hnorm) * familyRepresentation c a)
    rw [blockOperator_adjoint]
    apply diagonal_compact_of_zero_tail (familyHilbert c)
      (fun j => (star (c j).operator - (c j).operator) * (c j).representation a) _ N
    · intro x j
      rfl
    · exact fun j => (c j).adjoint_compact a
    · exact fun j hj => (htail j hj).2.2 a

theorem finiteActiveCycle_unital (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate)
    (hu : ∀ j, (c j).representation 1 = 1) :
    (finiteActiveCycle c C hC hnorm N htail).representation 1 = 1 := by
  change familyRepresentation c 1 = (1 : End (countableHilbertSpace (familyHilbert c)))
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change (c j).representation 1 (x j) = x j
  rw [hu]
  rfl

theorem finiteActiveCycle_selfAdjoint (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate)
    (hs : ∀ j, IsSelfAdjoint (c j).operator) :
    IsSelfAdjoint (finiteActiveCycle c C hC hnorm N htail).operator := by
  change IsSelfAdjoint (blockOperator (fun j => (c j).operator) C hC hnorm)
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr (fun j => (hs j).isSymmetric (x j) (y j))

theorem finiteActiveCycle_norm (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate) :
    ‖(finiteActiveCycle c C hC hnorm N htail).operator‖ ≤ C :=
  blockOperator_norm_le _ _ _ _

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HilbertHeadTail
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The head and tail decomposition used in finite-cycle telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace)

theorem head_tail_orthogonal :
    (summandIsometry H 0).toContinuousLinearMap.adjoint.comp
      (tailInsert H).toContinuousLinearMap = 0 := by
  rw [summandIsometry_adjoint]
  ext x
  rfl

theorem head_tail_exhaustive :
    (summandIsometry H 0).toContinuousLinearMap.comp
        (summandIsometry H 0).toContinuousLinearMap.adjoint +
      (tailInsert H).toContinuousLinearMap.comp (tailInsert H).toContinuousLinearMap.adjoint = 1 := by
  rw [summandIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change (lp.single (E := fun j => H j) 2 0 (x 0)) j +
    (tailInsert H ((tailInsert H).toContinuousLinearMap.adjoint x)) j = x j
  cases j with
  | zero =>
    rw [tailInsert_zero]
    simp
  | succ j =>
    rw [tailInsert_succ, tailInsert_adjoint_apply]
    simp

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HomogeneousReindex
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing repeated Hilbert summands for finite telescoping -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : HilbertSpace)

theorem blockOperator_reindex (e : ℕ ≃ ℕ) (T : ℕ → End H)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) :
    operatorConjugation (repeatedReindexEquiv H e).toLinearIsometry
      (blockOperator T C hC hT) =
    blockOperator (fun j => T (e.symm j)) C hC (fun j => hT (e.symm j)) := by
  have hadj : (repeatedReindexEquiv H e).toLinearIsometry.toContinuousLinearMap.adjoint =
      (repeatedReindexEquiv H e).symm.toLinearIsometry.toContinuousLinearMap :=
    (repeatedReindexEquiv H e).adjoint_eq_symm
  change (repeatedReindexEquiv H e).toLinearIsometry.toContinuousLinearMap.comp
      ((blockOperator T C hC hT).comp (repeatedReindexEquiv H e).toLinearIsometry.toContinuousLinearMap.adjoint) = _
  rw [hadj]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change T (e.symm j) (x (e (e.symm j))) = T (e.symm j) (x j)
  rw [e.apply_symm_apply]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OrthogonalExtensionBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity for orthogonal corners with an unused complementary summand -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]

theorem rationalBoundaryUnitary_orthogonalExtension
    (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R) (horth : ∀ a b, φ a * ψ b = 0)
    (F : A) (G : B) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    rationalBoundaryUnitary (nonunitalIdentityExtension (nonunitalOrthogonalSumHom φ ψ horth) (F, G))
      (nonunitalIdentityExtension_selfAdjoint _ _ (Prod.ext hF.star_eq hG.star_eq)) =
    nonunitalUnitaryExtension φ (rationalBoundaryUnitary F hF) *
      nonunitalUnitaryExtension ψ (rationalBoundaryUnitary G hG) := by
  have hp : IsSelfAdjoint (F, G) := Prod.ext hF.star_eq hG.star_eq
  have h := nonunital_rationalBoundaryUnitary (nonunitalOrthogonalSumHom φ ψ horth) (F, G) hp
  have hfst := map_rationalBoundaryUnitary (StarAlgHom.fst ℂ A B) (F, G) hp
  have hsnd := map_rationalBoundaryUnitary (StarAlgHom.snd ℂ A B) (F, G) hp
  change (rationalBoundaryUnitary (F, G) hp : A × B).1 = (rationalBoundaryUnitary F hF : A) at hfst
  change (rationalBoundaryUnitary (F, G) hp : A × B).2 = (rationalBoundaryUnitary G hG : B) at hsnd
  apply Subtype.ext
  rw [nonunitalUnitaryExtension_orthogonal φ ψ horth]
  change 1 + (φ ((rationalBoundaryUnitary (F, G) hp : A × B).1 - 1) +
    ψ ((rationalBoundaryUnitary (F, G) hp : A × B).2 - 1)) = _ at h
  rw [hfst, hsnd] at h
  simpa only [add_assoc] using h.symm

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsBoundaryDegeneracy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degenerate families have zero whole-union Roe boundary

Vanishing is proved from an exact global involution, not from vanishing of
the individual finite-component K-theory classes.
-/

noncomputable section

namespace CoarseAssembly

namespace Analytic

theorem localizedOperator_degenerate {A : Type} [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] (c : OddCycle A) (a : ι → A) (hc : c.Degenerate)
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    localizedOperator c a = c.operator := by
  apply sub_eq_zero.mp
  rw [localizedOperator_sub_eq c a hpart]
  simp only [hc.1, mul_zero, Finset.sum_const_zero]

end Analytic

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SampledHomotopy
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.circleRepresentation_coordinate _root_.OAI.CoarseAssembly.Analytic.compactIndexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.indexPairing_cycleClass _root_.OAI.CoarseAssembly.Analytic.intervalGrid_finish _root_.OAI.CoarseAssembly.Analytic.intervalGrid_start _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_succ _root_.OAI.CoarseAssembly.Analytic.lastEndpointFirst_zero _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.negativeProjection_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.pushforward_id _root_.OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero
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

def sampledCycle (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) : OddCycle A where
  space := h.space
  representation := if j < N then h.representation (τ j) else
    characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)
  operator := if j < N then h.operator (τ j) else 1
  commutator_compact a := by
    by_cases hj : j < N
    · simpa only [ite_eq_left hj] using h.commutator_compact (τ j) a
    · simp only [ite_eq_right hj, one_mul, mul_one, sub_self]
      exact isCompactOperator_zero
  square_compact a := by
    by_cases hj : j < N
    · simpa only [ite_eq_left hj] using h.square_compact (τ j) a
    · simp only [ite_eq_right hj, one_mul, sub_self, zero_mul]
      exact isCompactOperator_zero
  adjoint_compact a := by
    by_cases hj : j < N
    · simpa only [ite_eq_left hj] using h.adjoint_compact (τ j) a
    · simp only [ite_eq_right hj, star_one, sub_self, zero_mul]
      exact isCompactOperator_zero

theorem sampledCycle_inactive_degenerate (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) (hj : N ≤ j) :
    (sampledCycle h χ N τ j).Degenerate := by
  have he : sampledCycle h χ N τ j = identityOperatorCycle
      (characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) := by
    simp only [sampledCycle, identityOperatorCycle, ite_eq_right (not_lt.mpr hj)]
  rw [he]
  exact identityOperatorCycle_degenerate _

theorem sampledCycle_unital (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ)
    (hπ : ∀ t, h.representation t 1 = 1) :
    (sampledCycle h χ N τ j).representation 1 = 1 := by
  change (if j < N then h.representation (τ j) else
    characterProjectionRepresentation χ (1 : End h.space) (IsStarProjection.one _)) 1 = 1
  split_ifs with hj
  · exact hπ (τ j)
  · simp [characterProjectionRepresentation]

theorem sampledCycle_selfAdjoint (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ)
    (hs : ∀ t, IsSelfAdjoint (h.operator t)) :
    IsSelfAdjoint (sampledCycle h χ N τ j).operator := by
  change IsSelfAdjoint (if j < N then h.operator (τ j) else 1)
  split_ifs
  · exact hs (τ j)
  · exact IsSelfAdjoint.one _

theorem sampledCycle_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (j : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) : ‖(sampledCycle h χ N τ j).operator‖ ≤ C := by
  change ‖if j < N then h.operator (τ j) else 1‖ ≤ C
  split_ifs
  · exact hF (τ j)
  · exact ContinuousLinearMap.norm_id_le.trans hC

def sampledFiniteSum (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) : OddCycle A :=
  finiteActiveCycle (sampledCycle h χ N τ) C (zero_le_one.trans hC)
    (fun j => sampledCycle_norm_le h χ N τ j C hC hF) N
    (fun j => sampledCycle_inactive_degenerate h χ N τ j)

theorem sampledFiniteSum_selfAdjoint (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) (hs : ∀ t, IsSelfAdjoint (h.operator t)) :
    IsSelfAdjoint (sampledFiniteSum h χ N τ C hC hF).operator :=
  finiteActiveCycle_selfAdjoint _ _ _ _ _ _ (fun j => sampledCycle_selfAdjoint h χ N τ j hs)

theorem sampledFiniteSum_norm_le (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (N : ℕ) (τ : ℕ → Interval) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ t, ‖h.operator t‖ ≤ C) : ‖(sampledFiniteSum h χ N τ C hC hF).operator‖ ≤ C :=
  finiteActiveCycle_norm _ _ _ _ _ _

end CoarseAssembly.Analytic

end

end OAI
end


