-- Prove2me | Definitions.Def_OAIQ075A036
-- name    : OAIQ075A036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:59:37.401967+00:00
-- url     : https://prove2.me/theorems/1ee216df-ce2f-4a13-8adb-419447071f6c
-- title:
--   Definitions bundle OAIQ075A036 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 4 definitions and 16 theorems. The definitions and types are `OAI.KadisonSimilarity.FiniteFactorPresentation.model`, `OAI.KadisonSimilarity.concreteRealTracialSequence`, `OAI.KadisonSimilarity.concreteTracialExpectation`, `OAI.KadisonSimilarity.generatedFiniteFactorModel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixRefinement`, `KadisonSimilarity_Tracial_ConcreteMatrixTower`, `KadisonSimilarity_Tracial_ConcreteProjectionComparison`, `KadisonSimilarity_Tracial_ConcreteRealSequence`, `KadisonSimilarity_Tracial_ConcreteTracialExpectation`, `KadisonSimilarity_Tracial_ConstantMomentLimit`, `KadisonSimilarity_Tracial_FiniteFactorPresentation`, `KadisonSimilarity_Tracial_GeneratedFiniteFactorModel`, `KadisonSimilarity_Tracial_MatrixDiffuseSource`, `KadisonSimilarity_Tracial_MatrixStageGrowth`, `KadisonSimilarity_Tracial_NormalTracialInclusionModel`, `KadisonSimilarity_Tracial_RelativeMatrixQuantization`, `KadisonSimilarity_Tracial_SourceCornerQuantization`, `KadisonSimilarity_Tracial_TracialFactorComparison`, `KadisonSimilarity_Tracial_TracialInclusionModel`.
--
--   **Imports.** It imports the bundles `OAIQ075A031`, `OAIQ075A032`, `OAIQ075A033` and `OAIQ075A034` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A038`; the statements `OAI_KadisonSimilarity_CentralDecompositionData_matrix_bound`, `OAI_KadisonSimilarity_norm_commutator_le_generatedUltrapowerOperator`, `OAI_KadisonSimilarity_uniformCommutatorEstimate_of_published` and `OAI_KadisonSimilarity_universalHyperreflexivity_of_published`; the proofs of `OAI_KadisonSimilarity_CentralDecompositionData_matrix_bound`, `OAI_KadisonSimilarity_TracialCornerGeometry_exists_orthogonal_unitaries_of_normal_matrix_tower`, `OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower`, `OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation`, `OAI.KadisonSimilarity.canonicalFreeFactorComparison`, `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner`, `OAI_KadisonSimilarity_norm_commutator_le_generatedUltrapowerOperator`, `OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner`, `OAI_KadisonSimilarity_uniformCommutatorEstimate_of_published` and `OAI_KadisonSimilarity_universalHyperreflexivity_of_published`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A031
import Definitions.Def_OAIQ075A032
import Definitions.Def_OAIQ075A033
import Definitions.Def_OAIQ075A034

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Tracial
theorem exists_matrixAlgebra_for_unit_partition (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (Q : CornerPartition (identityProjection M)) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Generator.MatrixUnitSystem (Fin Q.size) M.toStarSubalgebra,
      (∀ i, E.entry i i=(Q.piece i).val) ∧
      Function.Injective E.hom ∧
      E.concreteAlgebra ≤ M.toStarSubalgebra ∧ WOTClosed E.concreteAlgebra := by
  obtain ⟨e,hd,hs,hm,hu⟩ := exists_matrixUnits_for_partition τ hfactor Q hn ht
  let E : Generator.MatrixUnitSystem (Fin Q.size) M.toStarSubalgebra := ⟨e,hs,hm,hu⟩
  have : Nontrivial M.toStarSubalgebra := by
    apply nontrivial_of_ne (0 : M.toStarSubalgebra) 1
    intro h
    have ht := congrArg τ.trace h
    have hz : τ.trace 0=0 := by simp [TracialRepresentation.trace]
    rw [hz,τ.trace_one] at ht
    exact zero_ne_one ht
  have : Nonempty (Fin Q.size) := ⟨⟨0,hn⟩⟩
  exact ⟨E,hd,E.injective,E.concreteAlgebra_le,E.concreteAlgebra_wotClosed⟩

end Tracial
end

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.restrictedTracialGNSInclusion_vector _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_commuting_matrix_extension
    (τ : TracialRepresentation M) (E : MatrixUnitSystem ι M.toStarSubalgebra) (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (n : ℕ) (hn : 0 < n) :
    ∃ F : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l),
        Function.Injective F.hom ∧
        (∀ j,τ.trace (F.entry j j)=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
        E.algebra ≤ (E.product F hc).algebra ∧
        WOTClosed (E.product F hc).concreteAlgebra := by
  let C := E.relativeVonNeumann
  let τC := restrictedTrace τ E.relativeVonNeumann_le
  obtain ⟨Q,hsize,ht⟩ := exists_uniform_trace_partition τC (E.relative_diffuse o hdiff)
    n (identityProjection C) (n : ℝ)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n)) (by
      change τC.trace 1=(n : ℂ)*(((n : ℝ)⁻¹ : ℝ) : ℂ)
      simp [τC.trace_one,hn.ne'])
  subst n
  obtain ⟨G,hdiag,hG,hGM,hGW⟩ := exists_matrixAlgebra_for_unit_partition τC
    (E.relative_scalar_center o hfactor) Q hn (fun i j => (ht i).trans (ht j).symm)
  let f := coordinateInclusion E.relativeVonNeumann_le
  let F := G.map f
  have hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l) := by
    intro i j k l
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry k l).val).mp (G.entry k l).property).2 i j
  refine ⟨F,hc,?_,?_,E.algebra_le_product_left F hc,
    (E.product F hc).concreteAlgebra_wotClosed⟩
  · intro a b hab
    apply hG
    have hm (a : Matrix (Fin Q.size) (Fin Q.size) ℂ) : F.hom a=f (G.hom a) := by
      simp only [MatrixUnitSystem.hom_apply,map_sum,map_smul]
      rfl
    rw [hm,hm] at hab
    exact (StarSubalgebra.inclusion_injective E.relativeVonNeumann_le) hab
  · intro j
    change τC.trace (G.entry j j)=_
    rw [hdiag]
    exact ht j

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteTracialExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact trace-pairing expectation consumed by the free-corner proof is
constructed on concrete finite tracial von Neumann inclusions and transported
through faithful algebra coordinates. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

section Concrete
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {N M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonSimilarity.expectationAlgebra_closed
def concreteTracialExpectation (τ : TracialRepresentation M) (hNM : N ≤ M) :
    TracialExpectation (concreteTraceLinear τ) (insideAlgebra (M := M) (P := N)) where
  map := (conditionalExpectationCLM τ hNM).toLinearMap
  range x := conditionalExpectation_mem τ hNM x
  pairing x c hc := by
    have h := conditionalExpectation_orthogonal τ hNM x ⟨c, hc⟩
    change τ.trace (c * (x - conditionalExpectation τ hNM x)) = 0 at h
    rw [mul_sub, trace_sub] at h
    exact (sub_eq_zero.mp h).symm

end Concrete

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteMatrixTower
attribute [-instance] _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate maps for the actual increasing matrix stages. These maps
retain the concrete operators and their normalized traces. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H}

variable (F : ℕ → FiniteMatrixStage N)

theorem generatedMatrixTrace_normal (υ : TracialRepresentation N) :
    HasNormalGNS (generatedMatrixTrace F υ) :=
  hasNormalGNS_of_predual (concretePredualEquiv (FiniteMatrixStage.generatedVonNeumann F))
    (generatedMatrixTrace F υ) (vectorPositiveFunctional_normal _ υ.vector)
    (generatedMatrixTrace_tracial F υ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact trace-comparison input used in the corner argument follows
from projection comparison in a concrete finite factor. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonSimilarity.comparisonAlgebra_closed
/-- In a finite factor, a projection of smaller trace embeds into the
larger projection. The partial isometry is constructed by the
maximality argument, and faithfulness removes the possible residual. -/
theorem finiteFactorProjectionComparison (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a * c = c * a) →
        ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra)) :
    FiniteFactorProjectionComparison (fun a : M.toStarSubalgebra => (τ.trace a).re) := by
  intro e r he hr htrace
  let p : AlgebraProjection M := ⟨r, hr⟩
  let q : AlgebraProjection M := ⟨e, he⟩
  obtain ⟨v, hvp, hvq, hfull⟩ := exists_partialIsometry_comparison τ hfactor p q
  have hsource : v.support = p := by
    rcases hfull with hs | ht
    · exact hs
    · apply projection_eq_of_le_of_trace_eq τ hvp
      rw [projection_trace_real τ v.support, projection_trace_real τ p]
      apply congrArg Complex.ofReal
      apply le_antisymm (concrete_projection_trace_mono τ hvp)
      rw [v.trace_support_eq_target τ, ht]
      exact htrace
  refine ⟨v.val, v.initial.trans (congrArg Subtype.val hsource), ?_⟩
  exact hvq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteRealSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyadic signs in a diffuse finite tracial von Neumann algebra form
the real tracial sequence required by the matrix-tower construction. The
underlying projections have compatible dyadic refinements and
orthogonality relations. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

/-- A concrete diffuse tracial von Neumann algebra supplies the full real
sequence without an independent orthonormal-sequence existence premise. -/
def concreteRealTracialSequence : RealTracialSequence (concreteTraceLinear τ) where
  vector := concreteRademacher τ hdiff
  trace_zero := concreteRademacher_trace τ hdiff
  selfadjoint := concreteRademacher_star τ hdiff
  inner := concreteRademacher_inner τ hdiff

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConstantMomentLimit
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-density promotes countable quotient moments to every constant coefficient. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower BoundedHochschild Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

theorem constantIntegerMoments_of_dense (d : ℕ → B) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hdense : ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
      GNSTendsto τ (fun k => d (j k)) atTop b)
    (u : ℕ → unitary B)
    (hu : AllQuotientMoments τ h1 ω tr (fun i => BoundedContinuousFunction.const ℕ (d i)) u) :
    ConstantIntegerMoments τ h1 ω tr u := by
  let T := quotientTrace τ h1 ω tr
  let φ := constant τ h1 ω tr
  let W := quotientUnitary τ h1 ω tr u
  have hm (a : Option ℕ) (l : List (IntAtom ℕ)) (hl : admissibleIntTail l)
      (hk : ∀ b ∈ l, b.1 ≠ 0) :
      T (integerEval (fun n => φ (d n) - T (φ (d n)) • 1) W a l) = 0 :=
    integer_moments_of_bounded T (fun n => φ (d n) - T (φ (d n)) • 1) W hu a l hl hk
  intro a l hl hk
  have hz := all_integer_moments_of_trace_dense τ T (quotientTrace_one τ h1 ω tr)
    (quotientTrace_tracial τ h1 ω tr) φ (quotientTrace_constant τ h1 ω tr)
    d hd hdense W hm (fun x : B => x) a l hl hk
  simpa only [φ, T, quotientTrace_constant] using hz

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialFactorComparison
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison in the finite-matrix source follows from its
actual normal trace and dense full-matrix tower. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

namespace TracialCornerGeometry
variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.normalFactor_closed
theorem projectionComparison_of_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (N : VonNeumannAlgebra H)
    (hN : G.left.range = N.toStarSubalgebra)
    (hfactor : ∀ c : P, (∀ a : P, a * c = c * a) → ∃ z : ℂ, c = z • (1 : P)) :
    FiniteFactorProjectionComparison (fun a => (G.trace a).re) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hfactorN : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, a * c = c * a) →
        ∃ z : ℂ, c = z • (1 : N.toStarSubalgebra) := by
    intro c hc
    obtain ⟨b, rfl⟩ := e.surjective c
    change ∀ a : N.toStarSubalgebra, a * e b = e b * a at hc
    have hb (a : P) : a * b = b * a := by
      apply e.injective
      change e (a * b) = e (b * a)
      rw [map_mul e a b, map_mul e b a]
      exact hc (e a)
    obtain ⟨z, hz⟩ := hfactor b hb
    refine ⟨z, ?_⟩
    change e b = z • (1 : N.toStarSubalgebra)
    rw [hz, map_smul, map_one]
  exact finiteFactorProjectionComparison_of_equiv e
    (fun a => (G.trace a).re) (fun a => (τ.trace a).re)
    (fun a => congrArg Complex.re (G.normalTracialRepresentation_trace h1 hf N hN a))
    (finiteFactorProjectionComparison τ hfactorN)

end TracialCornerGeometry

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  (τ : R →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τ.toLinearMap (gnsTracialVector τ))
  (hnormal : τ.gnsStarAlgHom.range =
    (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra)

include h1 htr hf M hnormal in
/-- The comparison input for every matrix size in the actual source model. -/
theorem matrix_projectionComparison_of_tower (n : ℕ) [NeZero n] :
    FiniteFactorProjectionComparison
      (fun X : CStarMatrix (Fin n) (Fin n) R => (normalizedMatrixTrace τ n X).re) := by
  let G := gnsTracialGeometry τ htr
  have hcenter : ∀ c : R, (∀ a : R, c * a = a * c) →
      ∃ z : ℂ, c = algebraMap ℂ R z := by
    intro c hc
    obtain ⟨z, hz⟩ := G.scalar_center_of_matrix_tower M (gnsTracialVector_injective τ hf)
      c (fun a => (hc a).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hid (X : CStarMatrix (Fin n) (Fin n) R) :
      matrixEntryHom (StarAlgHom.id ℂ R) X = X := by
    ext i j
    rfl
  have hcenterN : ∀ X : CStarMatrix (Fin n) (Fin n) R,
      (∀ Y, Y * X = X * Y) → ∃ z : ℂ, X = z • (1 : CStarMatrix (Fin n) (Fin n) R) := by
    intro X hX
    obtain ⟨z, hz⟩ := scalar_of_matrix_relative_commutant (StarAlgHom.id ℂ R)
      hcenter X (fun Y => by rw [hid]; exact (hX Y).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  let Gn := gnsTracialGeometry (normalizedMatrixTrace τ n) (normalizedMatrixTrace_tracial τ htr)
  exact Gn.projectionComparison_of_normal_range (normalizedMatrixTrace_one τ h1)
      (gnsTracialVector_injective _ (normalizedMatrixTrace_faithful τ hf)) _
      (matrix_gns_normal_range τ _ hnormal n) hcenterN

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixStageGrowth
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full finite matrix stage has a minimal diagonal projection. This
is the obstruction to a diffuse generated algebra stabilizing at a stage. -/

noncomputable section
namespace KadisonSimilarity

open Generator

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]

theorem concreteStage_eq_of_size_eq {E F : FiniteMatrixStage N}
    (h : E.units.concreteAlgebra ≤ F.units.concreteAlgebra) (hs : E.size = F.size) :
    E.units.concreteAlgebra = F.units.concreteAlgebra := by
  have hd : Module.finrank ℂ E.units.concreteAlgebra =
      Module.finrank ℂ F.units.concreteAlgebra := by
    rw [concreteStage_finrank, concreteStage_finrank, hs]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := (StarSubalgebra.inclusion h).toLinearMap)).mp (StarSubalgebra.inclusion_injective h)
  apply le_antisymm h
  intro c hc
  obtain ⟨a, ha⟩ := hsurj ⟨c, hc⟩
  have he : (a : H →L[ℂ] H) = c :=
    congrArg (fun b : F.units.concreteAlgebra => (b : H →L[ℂ] H)) ha
  rw [← he]
  exact a.property

theorem matrix_stage_sizes_cofinal (F : ℕ → FiniteMatrixStage N)
    (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) :
    ∀ b : ℕ, ∃ n, b ≤ (F n).size := by
  intro b
  by_contra hb
  have hlt (n : ℕ) : (F n).size < b :=
    Nat.lt_of_not_ge (fun h => hb ⟨n, h⟩)
  let S : Set ℕ := Set.range (fun n => (F n).size)
  have hS : S.Nonempty := ⟨(F 0).size, 0, rfl⟩
  have hB : BddAbove S := ⟨b, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem hS hB
  change (F n₀).size = sSup S at hn₀
  have hmax (n : ℕ) : (F n).size ≤ (F n₀).size := by
    rw [hn₀]
    exact le_csSup hB ⟨n, rfl⟩
  have hstage (n : ℕ) : (F n).units.concreteAlgebra ≤ (F n₀).units.concreteAlgebra := by
    have hs : (F n₀).size = (F (max n n₀)).size :=
      le_antisymm (concreteStage_size_le (hmono (Nat.le_max_right n n₀))) (hmax _)
    have he := concreteStage_eq_of_size_eq (hmono (Nat.le_max_right n n₀)) hs
    exact (hmono (Nat.le_max_left n n₀)).trans (le_of_eq he.symm)
  apply generated_ne_stage_of_diffuse F hdiff n₀
  exact le_antisymm
    (FiniteMatrixStage.generated_minimal F _ (F n₀).units.concreteAlgebra_wotClosed hstage)
    (FiniteMatrixStage.stage_le_generated F n₀)

/-- Diffuseness forces exactly the diverging matrix sizes needed in the
finite-factor commutator argument. -/
theorem matrix_stage_sizes_tendsto (F : ℕ → FiniteMatrixStage N)
    (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) :
    Filter.Tendsto (fun n => (Fintype.card (Fin (F n).size) : ℝ))
      Filter.atTop Filter.atTop := by
  have hn : Filter.Tendsto (fun n => (F n).size) Filter.atTop Filter.atTop :=
    (show Monotone (fun n => (F n).size) from fun _ _ h =>
      concreteStage_size_le (hmono h)).tendsto_atTop_atTop
        (matrix_stage_sizes_cofinal F hmono hdiff)
  convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp hn using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_apply, Fintype.card_fin]

end Concrete

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedFiniteFactorModel
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed matrix subfactor in a normal trace representation
supplies the finite-factor model in the original representation. Only the
prescribed ultrapower free position remains a local input. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {P : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (υ : TracialRepresentation N)
  (e : P.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
  (he : ∀ a, υ.trace (e a) = τ a) (F : ℕ → FiniteMatrixStage N)

variable [Nontrivial N.toStarSubalgebra]
  (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hnormal : HasNormalGNS τ)
  (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
  (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
    IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
      p * q = q ∧ q * p = q)
  (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
  (free_position : FiniteFactorFreeCornerInputs (generatedMatrixTrace F υ) τ
    (generatedMatrixTrace_one F υ) h1 ω (generatedMatrixTrace_tracial F υ) htr
    (generatedOriginalInclusion e F) (generatedOriginalInclusion_trace τ υ e he F) hω)

attribute [local instance] OAI.KadisonSimilarity.generatedStageNonempty
/-- No matrix presentation, matrix-size divergence, or source-trace
properties are assumed separately from the constructed diffuse subfactor. -/
def generatedFiniteFactorModel : FiniteFactorModel P where
  R := (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra
  traceR := generatedMatrixTrace F υ
  traceP := τ
  oneR := generatedMatrixTrace_one F υ
  oneP := h1
  tracialR := generatedMatrixTrace_tracial F υ
  tracialP := htr
  faithfulR := generatedMatrixTrace_faithful F υ
  faithfulP := hf
  normalR := generatedMatrixTrace_normal F υ
  normalP := hnormal
  inclusion := generatedOriginalInclusion e F
  trace_inclusion := generatedOriginalInclusion_trace τ υ e he F
  size := fun n => (F n).size
  stageNonempty := generatedStageNonempty F
  matrices := concreteNestedTracialMatrices F hmono υ
  size_tendsto := matrix_stage_sizes_tendsto F hmono hdiff
  omega := ω
  omega_cofinite := hω
  localInputs := free_position

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorPresentation
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite diffuse branch has a constructed normal trace and an actual
irreducible matrix source. Its sole remaining local input is Popa freeness. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

attribute [instance] FiniteFactorPresentation.normed FiniteFactorPresentation.innerProduct
  FiniteFactorPresentation.complete

namespace FiniteFactorPresentation
variable {P} (F : FiniteFactorPresentation P)

attribute [local instance] OAI.KadisonSimilarity.finitePresentationClosed
def model (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hfree : F.FreePosition ω hω) : FiniteFactorModel P := by
  let e := F.equivalence
  let : Nontrivial F.N.toStarSubalgebra :=
    nontrivial_of_ne (e 0) (e 1) (fun h => by
      have he : (0 : P.toStarSubalgebra) = 1 := e.injective h
      have ht := congrArg F.traceData.trace he
      rw [map_zero, F.traceData.one] at ht
      exact zero_ne_one ht)
  exact generatedFiniteFactorModel F.traceData.trace F.representation F.equivalence
    F.trace_equivalence F.source.stages F.traceData.one F.traceData.tracial
    F.traceData.faithful F.normal F.source.monotone F.source.source_factor.diffuse ω hω hfree

end FiniteFactorPresentation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixDiffuseSource
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison and small diagonal matrix corners show that each
finite matrix amplification of the prescribed source is diffuse. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (tr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τ.toLinearMap (gnsTracialVector τ))
  (hnormal : τ.gnsStarAlgHom.range =
    (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

include h1 tr hf M hnormal hsize in
theorem matrix_diffuse_of_tower (n : ℕ) [NeZero n]
    (p : CStarMatrix (Fin n) (Fin n) A) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  let τn := normalizedMatrixTrace τ n
  let G := gnsTracialGeometry τn (normalizedMatrixTrace_tracial τ tr)
  apply G.proper_subprojection_of_small_trace
    (gnsTracialVector_injective τn (normalizedMatrixTrace_faithful τ hf))
    (matrix_projectionComparison_of_tower τ h1 tr hf M hnormal n) ?_ p hp hp0
  intro s hs
  obtain ⟨m, _, t, ht, hts, F, hF⟩ := M.exists_small_trace_frame hsize hs
  change τ F.corner = (t : ℂ) at hF
  refine ⟨matrixDiagonalHom n F.corner, F.corner_projection.map (matrixDiagonalHom n), ?_, ?_⟩
  · change 0 < (τn (matrixDiagonalHom n F.corner)).re
    rw [normalizedMatrixTrace_diagonal, hF, Complex.ofReal_re]
    exact ht
  · change (τn (matrixDiagonalHom n F.corner)).re < s
    rw [normalizedMatrixTrace_diagonal, hF, Complex.ofReal_re]
    exact hts

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInclusionModel
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous normal representations of a trace-preserving inclusion.
The source range is proved closed, retaining the given source algebra. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

attribute [instance] TracialInclusionModel.normed TracialInclusionModel.innerProduct
  TracialInclusionModel.complete

/-- Both given algebras occur as normal ranges on one Hilbert space. -/
theorem exists_tracialInclusionModel
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (eA : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (eB : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] B)
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hnA : BoundedHochschild.TraceInPredual eA τA)
    (hnB : BoundedHochschild.TraceInPredual eB τB)
    (h1B : τB 1 = 1) (htrB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (ht : ∀ a, τB (φ a) = τA a) : Nonempty (TracialInclusionModel φ τB) := by
  let hnormal := hasNormalGNS_of_predual eB τB hnB htrB
  let M := representationVonNeumannAlgebra τB.gnsStarAlgHom
  let υ := normalGNSRepresentation τB h1B htrB hfB hnormal
  let f := normalGNSEquivalence τB htrB hfB hnormal
  have hf (b : B) : υ.trace (f b) = τB b :=
    normalGNSRepresentation_trace τB h1B htrB hfB hnormal b
  let ψ : A →⋆ₐ[ℂ] M.toStarSubalgebra := f.toStarAlgHom.comp φ
  have hψ (a : A) : υ.trace (ψ a) = τA a := (hf (φ a)).trans (ht a)
  let σ := M.toStarSubalgebra.subtype.comp ψ
  let N := representationVonNeumannAlgebra σ
  have hrange : σ.range = N.toStarSubalgebra :=
    tracialInclusion_normal_range_of_predual υ τA ψ hψ eA hnA
  have hNM : N ≤ M := by
    intro x hx
    have hx' : x ∈ σ.range := by rw [hrange]; exact hx
    obtain ⟨a, rfl⟩ := hx'
    exact (ψ a).property
  have hσ : Function.Injective σ := by
    intro a b hab
    apply hi
    apply f.injective
    exact Subtype.ext hab
  let g := equivalenceOfConcreteRange N σ hσ hrange
  refine ⟨{
    K := τB.GNS
    N := N
    M := M
    le := hNM
    representation := υ
    sourceEquiv := g
    ambientEquiv := f
    compatible := fun a => ?_
    trace_eq := hf }⟩
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalTracialInclusionModel
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common normal model from closed trace-vector balls. This formulation
applies directly to normalized finite matrix traces. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem exists_tracialInclusionModel_of_trace_balls
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τA '' Metric.closedBall (0 : A) C))
    (h1B : τB 1 = 1) (htrB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (hnormal : HasNormalGNS τB)
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (ht : ∀ a, τB (φ a) = τA a) : Nonempty (TracialInclusionModel φ τB) := by
  let M := representationVonNeumannAlgebra τB.gnsStarAlgHom
  let υ := normalGNSRepresentation τB h1B htrB hfB hnormal
  let f := normalGNSEquivalence τB htrB hfB hnormal
  have hf (b : B) : υ.trace (f b) = τB b :=
    normalGNSRepresentation_trace τB h1B htrB hfB hnormal b
  let ψ : A →⋆ₐ[ℂ] M.toStarSubalgebra := f.toStarAlgHom.comp φ
  have hψ (a : A) : υ.trace (ψ a) = τA a := (hf (φ a)).trans (ht a)
  let σ := M.toStarSubalgebra.subtype.comp ψ
  let N := representationVonNeumannAlgebra σ
  have hrange : σ.range = N.toStarSubalgebra :=
    tracialInclusion_normal_range υ τA ψ hψ hclosed
  have hNM : N ≤ M := by
    intro x hx
    have hx' : x ∈ σ.range := by rw [hrange]; exact hx
    obtain ⟨a, rfl⟩ := hx'
    exact (ψ a).property
  have hσ : Function.Injective σ := by
    intro a b hab
    apply hi
    apply f.injective
    exact Subtype.ext hab
  let g := equivalenceOfConcreteRange N σ hσ hrange
  refine ⟨{
    K := τB.GNS
    N := N
    M := M
    le := hNM
    representation := υ
    sourceEquiv := g
    ambientEquiv := f
    compatible := fun a => ?_
    trace_eq := hf }⟩
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_RelativeMatrixQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative finite matrix averaging in an irreducible inclusion. The matrix
systems stay in the prescribed source algebra throughout the refinement. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]
  (υ : TracialRepresentation M) (hNM : N ≤ M)
  (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c = c * coordinateInclusion hNM a) →
    ∃ z : ℂ, c = z • 1)

local instance relativeMatrixAmbientClosed_r362050_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.relativeMatrixSourceClosed
include υ hNM hfactor hdiff in
omit [Nontrivial N.toStarSubalgebra] in
/-- Every required finite size occurs in the diffuse source; no separable
matrix tower is needed for the local estimate. -/
theorem exists_source_matrix_stage (n : ℕ) (hn : 0 < n) :
    ∃ E : FiniteMatrixStage N, E.size = n := by
  obtain ⟨E, _⟩ := exists_commuting_matrix_extension (restrictedTrace υ hNM)
    (FiniteMatrixStage.scalarStage N).units ⟨0, Nat.zero_lt_one⟩ hfactor hdiff n hn
  exact ⟨⟨n, hn, E⟩, rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceCornerQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local quantization inside every nonzero corner of the prescribed source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildCorners
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

local instance sourceCornerAmbientClosed_r362050_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.sourceCornerSourceClosed
include υ hNM in
/-- Scalar center of a nonzero source corner. -/
theorem source_corner_factor
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∀ c : Corner p hp, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1 := by
  let τN := vectorPositiveFunctional N υ.vector
  have hfN (a : N.toStarSubalgebra) (ha : τN (star a * a) = 0) : a = 0 := by
    apply (restrictedTrace υ hNM).separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace (restrictedTrace υ hNM) a a).trans ha)
  have hdN : HochschildDiffuse.NoMinimalProjections N.toStarSubalgebra := by
    intro q hq hq0
    obtain ⟨r, hr, hr0, hrq, hqr, _⟩ := hdiff q hq hq0
    exact ⟨r, hr, (hr.le_iff_mul_eq_right hq).mpr hqr, hr0, hrq⟩
  have hcN := corner_factor p hp (concretePredualEquiv N) τN
    (vectorPositiveFunctional_normal N υ.vector)
    (vectorPositiveFunctional_one N υ.vector υ.norm_vector)
    (restrictedTrace υ hNM).trace_mul_comm hfN
    (fun b hb => hfactor b (fun a => (hb a).eq.symm)) hdN hp0
  exact fun c hc => hcN c (fun a => (hc a).symm)

/-- Compression of a centered corner element in the original coordinates. -/
theorem sourceCorner_compressed_eq (p : N.toStarSubalgebra) (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) (x : M.toStarSubalgebra) (c : ℂ) :
    let φ := coordinateInclusion hNM
    let ψ := sourceCornerHom φ p hp
    ((ψ q * (⟨φ p * x * φ p, compress_mem_corner (hp.map φ) x⟩ - c • 1) * ψ q :
      Corner (φ p) (hp.map φ)) : M.toStarSubalgebra) =
        φ (q : N.toStarSubalgebra) * x * φ (q : N.toStarSubalgebra) -
          c • φ (q : N.toStarSubalgebra) := by
  let φ := coordinateInclusion hNM
  have hqm : φ (q : N.toStarSubalgebra) * φ p = φ (q : N.toStarSubalgebra) := by
    rw [← map_mul, q.property.2]
  have hmq : φ p * φ (q : N.toStarSubalgebra) = φ (q : N.toStarSubalgebra) := by
    rw [← map_mul, q.property.1]
  have hqM := (corner_projection_coe p hp hq).map φ
  change φ (q : N.toStarSubalgebra) * (φ p * x * φ p - c • φ p) *
    φ (q : N.toStarSubalgebra) = _
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hqm, hqM.isIdempotentElem.eq]
  congr 1
  rw [← mul_assoc, ← mul_assoc, hqm, mul_assoc, hmq]

end KadisonSimilarity

end

end OAI
end


