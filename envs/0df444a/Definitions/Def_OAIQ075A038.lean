-- Prove2me | Definitions.Def_OAIQ075A038
-- name    : OAIQ075A038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:11:48.690985+00:00
-- url     : https://prove2.me/theorems/7225d4ca-daa1-4a0f-99f3-8f5eacda2d69
-- title:
--   Definitions bundle OAIQ075A038 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 2 definitions and 12 theorems. The definitions and types are `OAI.KadisonSimilarity.HiaiNormalStandardEmbeddingInput`, `OAI.KadisonSimilarity.countableSingleIsometry`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_MatrixSequence`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean), [`FactorGeneration_Subfactors`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Subfactors.lean), [`KadisonSimilarity_Representation_ConcreteIrreducibleSubfactor`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/ConcreteIrreducibleSubfactor.lean), [`KadisonSimilarity_Representation_NormalRepresentationReduction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/NormalRepresentationReduction.lean), [`KadisonSimilarity_Representation_StandardEmbeddingAssembly`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/StandardEmbeddingAssembly.lean), [`KadisonSimilarity_Tracial_RelativeMatrixQuantization`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/RelativeMatrixQuantization.lean), [`KadisonSimilarity_Tracial_SourceCornerQuantization`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceCornerQuantization.lean), [`KadisonSimilarity_Tracial_SourceMomentConstruction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/SourceMomentConstruction.lean), [`KadisonSimilarity_Tracial_TracialInclusionQuantization`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialInclusionQuantization.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A035` and `OAIQ075A036` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A039`; the proof of `OAI.KadisonSimilarity.FiniteFactorModel.estimate`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A035
import Definitions.Def_OAIQ075A036

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include τ hirr in
/-- A self-adjoint element of the relative corner commutant is scalar in
that corner, including the zero corner. -/
theorem selfAdjoint_corner_commutant_scalar (p : AlgebraProjection M)
    (c : M.toStarSubalgebra) (hc : IsSelfAdjoint c)
    (hl : p.val*c=c) (hr : c*p.val=c)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∃ z : ℂ, c=z • p.val := by
  let L : Submodule ℂ M.toStarSubalgebra := Submodule.span ℂ {p.val}
  have hclosed : IsClosed (L : Set M.toStarSubalgebra) := L.closed_of_finiteDimensional
  have hcL : c ∈ closure (L : Set M.toStarSubalgebra) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q,d,hfix,hQ,hd⟩ :=
      exists_finite_spectral_approximation_preserving_commutant p c hc ε hε
    have hpieces (i : Fin Q.size) : (Q.piece i).val ∈ L := by
      have htriv := corner_commutant_projection_trivial τ P hirr p (Q.piece i)
        (Q.piece_le i) (fun a => hQ (p.val*(a : M.toStarSubalgebra)*p.val)
          (hcomm a) (by
            show p.val*(p.val*(a : M.toStarSubalgebra)*p.val)=
              (p.val*(a : M.toStarSubalgebra)*p.val)*p.val
            simp only [← mul_assoc,p.property.isIdempotentElem.eq]
            simp only [mul_assoc,p.property.isIdempotentElem.eq]) i)
      rcases htriv with h | h
      · rw [h]; exact L.zero_mem
      · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨∑ i, (d i : ℂ) • (Q.piece i).val,
      L.sum_mem (fun i _ => L.smul_mem _ (hpieces i)),?_⟩
    simpa only [dist_eq_norm,hl,hr] using hd
  have hm : c ∈ L := by
    change c ∈ (L : Set M.toStarSubalgebra)
    rw [← hclosed.closure_eq]
    exact hcL
  exact Submodule.mem_span_singleton.mp hm |>.imp (fun z hz => hz.symm)

include τ hirr in
/-- Exact irreducibility in pMp, stated in ambient coordinates. The scalar
is the normalized corner trace when p is nonzero. -/
theorem corner_commutant_scalar (p : AlgebraProjection M) (c : M.toStarSubalgebra)
    (hl : p.val*c=c) (hr : c*p.val=c)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∃ z : ℂ, c=z • p.val := by
  have hsl : p.val*star c=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hr
  have hsr : star c*p.val=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hl
  have hstar := corner_commutant_star P p c hcomm
  have hreal : ∀ a : P, Commute (ℜ c : M.toStarSubalgebra)
      (p.val*(a : M.toStarSubalgebra)*p.val) := by
    intro a
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hstar a)).smul_left (2 : ℝ)⁻¹
  have himag : ∀ a : P, Commute (ℑ c : M.toStarSubalgebra)
      (p.val*(a : M.toStarSubalgebra)*p.val) := by
    intro a
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hstar a)).smul_left (2 : ℝ)⁻¹).smul_left (-Complex.I)
  obtain ⟨a,ha⟩ := selfAdjoint_corner_commutant_scalar τ P hirr p (ℜ c)
    (ℜ c).property (by simp [realPart_apply_coe,mul_add,hl,hsl])
    (by simp [realPart_apply_coe,add_mul,hr,hsr]) hreal
  obtain ⟨b,hb⟩ := selfAdjoint_corner_commutant_scalar τ P hirr p (ℑ c)
    (ℑ c).property (by simp [imaginaryPart_apply_coe,mul_sub,hl,hsl])
    (by simp [imaginaryPart_apply_coe,sub_mul,hr,hsr]) himag
  refine ⟨a+Complex.I*b,?_⟩
  calc c = (ℜ c : M.toStarSubalgebra)+Complex.I • (ℑ c : M.toStarSubalgebra) :=
      (realPart_add_I_smul_imaginaryPart c).symm
    _ = (a+Complex.I*b) • p.val := by rw [ha,hb,smul_smul,add_smul]

end

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generated_isII1 (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
      c=τ.trace c • (1 : M.toStarSubalgebra)) : IsII1Factor (generated A) := by
  apply irreducible_subalgebra_isII1 (restrictedTrace τ hNM) (generatedVonNeumann_le A) hdiff
  intro c hc
  have h := hirr (coordinateInclusion hNM c) (fun a =>
    congrArg (fun b : N.toStarSubalgebra => b.val) (hc a))
  refine ⟨τ.trace (coordinateInclusion hNM c),?_⟩
  exact Subtype.ext (congrArg (fun b : M.toStarSubalgebra => b.val) h)

theorem exists_irreducible_matrix_generated_II1
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
      IsII1Factor (generated A) ∧ generated A ≤ N.toStarSubalgebra ∧
      ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  obtain ⟨A,hA,hmono,hfd,_,hAN,hscalar⟩ :=
    exists_irreducible_matrix_generated_algebra τ hNM hfactor hdiff hirr hsep
  exact ⟨A,hA,hmono,hfd,generated_isII1 A τ hNM hdiff hscalar,hAN,hscalar⟩

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcreteIrreducibleSubfactor
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irreducible increasing matrix subfactors in the normal tracial GNS
representation. The matrix refinement theorem is applied after deriving
separability of that representation from the given predual. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (τ : A →ₚ[ℂ] ℂ)

/-- The irreducible hyperfinite presentation is constructed in the faithful
normal GNS representation of a diffuse finite factor. -/
theorem exists_gns_irreducible_matrix_subfactor
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hf : ∀ a, τ (star a * a) = 0 → a = 0)
    (hnormal : BoundedHochschild.TraceInPredual e τ)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : A))
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    let N := representationVonNeumannAlgebra τ.gnsStarAlgHom
    ∃ F : ℕ → FiniteMatrixStage N,
      F 0 = FiniteMatrixStage.scalarStage N ∧
      Monotone (fun n => (F n).units.concreteAlgebra) ∧
      (∀ n, FiniteDimensional ℂ (F n).units.concreteAlgebra) ∧
      IsII1Factor (FiniteMatrixStage.generated F) ∧
      FiniteMatrixStage.generated F ≤ N.toStarSubalgebra ∧
      ∀ c : N.toStarSubalgebra,
        (∀ a : FiniteMatrixStage.generated F, a.val * c.val = c.val * a.val) →
        ∃ z : ℂ, c = z • (1 : N.toStarSubalgebra) := by
  let N := representationVonNeumannAlgebra τ.gnsStarAlgHom
  let G := gnsTracialGeometry τ htr
  have hN : G.left.range = N.toStarSubalgebra := hasNormalGNS_of_predual e τ hnormal htr
  let υ := G.normalTracialRepresentation h1 (gnsTracialVector_injective τ hf) N hN
  let f := equivalenceOfConcreteRange N G.left
    (G.left_injective (gnsTracialVector_injective τ hf)) hN
  let := gns_separable_of_predual e τ hnormal
  have hcenter := scalar_center_of_starEquiv f hfactor
  have hdiffN := diffuse_projections_of_starEquiv f hdiff
  obtain ⟨F, hF0, hmono, hfd, hII, hFN, hirr⟩ :=
    FiniteMatrixStage.exists_irreducible_matrix_generated_II1 υ le_rfl hcenter hdiffN
      (fun c hc => hcenter c (fun a => by
        have h := hc a
        change a * c = c * a at h
        exact h))
      (TopologicalSpace.IsSeparable.of_separableSpace _)
  exact ⟨F, hF0, hmono, hfd, hII, hFN, fun c hc => ⟨υ.trace c, hirr c hc⟩⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalRepresentationReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normal representations and countable tracial multiplicity

The published input below is local to a fixed finite von Neumann algebra with
faithful normal finite trace and a fixed normal representation on a separable
Hilbert space.  Hiai, *Concise lectures on selected topics of von Neumann
algebras*, arXiv:2004.02383v1 (2020), Corollary 5.14 and Remark 5.15, printed
page 50, represent every normal positive functional by a vector in the tracial
standard form.  Applied on each cyclic reducing summand, the usual countable
cyclic decomposition gives the displayed isometric intertwiner.  This is the
normal-representation consequence used in the manuscript's global section;
it is not asserted here for arbitrary C-star representations or arbitrary
positive functionals.  The countable cyclic decomposition is the standard
representation theory cited there to Takesaki, *Theory of Operator Algebras I*
(1979).

All commutator and matrix estimates below are derived from that geometric
input and the already proved finite-to-countable transfer.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The precise local standard-form embedding consequence of Hiai
Corollary 5.14 / Remark 5.15 and countable cyclic decomposition.  At the
published application `τ` is the faithful normal trace of a finite von
Neumann algebra and `σ` is a normal representation on separable `H`.
The range is reducing because both representations preserve adjoints. -/
def HiaiNormalStandardEmbeddingInput (τ : A →ₚ[ℂ] ℂ)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∃ I : H →ₗᵢ[ℂ] CountableCopies τ.GNS,
    ∀ a, I.toContinuousLinearMap.comp (σ a) =
      (countableRepresentation τ.gnsStarAlgHom a).comp I.toContinuousLinearMap

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_StandardEmbeddingAssembly
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble embeddings of the cyclic summands into the countable standard
representation. The countability and Hilbert-sum construction are proved;
only the embeddings of the individual cyclic representations are parameters. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
def countableSingleIsometry (n : ℕ) : K →ₗᵢ[ℂ] CountableCopies K where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => K) 2 n).toLinearMap
  norm_map' x := by
    change ‖lp.single (E := fun _ : ℕ => K) 2 n x‖ = ‖x‖
    exact lp.norm_single (p := 2) (E := fun _ : ℕ => K) (by norm_num) n x

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_RelativeMatrixQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.normalRestriction_apply _root_.OAI.KadisonSimilarity.normalRestriction_coefficient _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector
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

local instance relativeMatrixAmbientClosed_r2ea6a4_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.relativeMatrixSourceClosed
include hfactor hdiff hirr in
theorem exists_relative_matrix_expectation_budget {I : Type*} [Fintype I]
    (x : I → M.toStarSubalgebra) (hx : ∀ i, υ.trace (x i) = 0)
    (E : FiniteMatrixStage N) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage N, E.size ≤ F.size ∧
      (∑ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        ((matrixSystemOfUnits (F.units.map (coordinateInclusion hNM))).expectation (x i))‖ ^ 2) < ε := by
  obtain ⟨F, hEF, hF⟩ := FiniteMatrixStage.exists_finite_matrix_energy_budget
    υ hNM hfactor hdiff hirr Finset.univ x (fun i _ => hx i) E ε hε
  refine ⟨F, matrix_stage_size_le_of_algebra_le hEF, ?_⟩
  simpa only [matrix_stage_energy_eq] using hF

include hfactor hdiff hirr in
/-- Relative local quantization with a small projection in the prescribed
source, using its cofinal family of finite matrix stages. -/
theorem exists_source_small_projection {I : Type*} [Fintype I]
    (T : ℕ → FiniteMatrixStage N) (hT : ∀ m : ℕ, ∃ j, m < (T j).size)
    (x : I → M.toStarSubalgebra) (hx : ∀ i, υ.trace (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧
      (υ.trace (coordinateInclusion hNM q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q)‖ ^ 2 <
          δ * (υ.trace (coordinateInclusion hNM q)).re := by
  let ρ := vectorPositiveFunctional M υ.vector
  let B : ℝ := ∑ i, ‖ρ.toPreGNS (x i)‖ ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (2 * B / δ) (1 / η))
  obtain ⟨j, hj⟩ := hT m
  obtain ⟨E, hTE, hE⟩ := exists_relative_matrix_expectation_budget υ hNM hfactor hdiff hirr
    x hx (T j) (δ / 2) (by positivity)
  have hmn : m < E.size := hj.trans_le hTE
  have hn : (0 : ℝ) < E.size := by exact_mod_cast E.positive
  have hBsmall : B / (E.size : ℝ) < δ / 2 := by
    have hlt : 2 * B / δ < (E.size : ℝ) :=
      (le_max_left _ _).trans_lt (hm.trans (by exact_mod_cast hmn))
    have hh := (div_lt_iff₀ hδ).mp hlt
    apply (div_lt_iff₀ hn).mpr
    nlinarith
  have hbudget : (∑ i,
      (‖ρ.toPreGNS
          ((matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))).expectation (x i))‖ ^ 2 +
        ‖ρ.toPreGNS (x i)‖ ^ 2 / (E.size : ℝ))) < δ := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    change _ + B / (E.size : ℝ) < δ
    linarith
  obtain ⟨q, hq, hq0, ht, hc⟩ := exists_source_rankOne_compression υ hNM E x hbudget
  refine ⟨q, hq, hq0, ?_, hc⟩
  rw [ht]
  have he : (E.size : ℂ)⁻¹ = Complex.ofReal ((E.size : ℝ)⁻¹) := by simp
  rw [he, Complex.ofReal_re]
  apply (inv_lt_comm₀ hn hη).mpr
  have hlt : 1 / η < (E.size : ℝ) :=
    (le_max_right _ _).trans_lt (hm.trans (by exact_mod_cast hmn))
  simpa only [one_div] using hlt

include hfactor hdiff hirr in
/-- Relative local quantization without a chosen matrix tower. -/
theorem exists_source_small_projection_of_diffuse {I : Type*} [Fintype I]
    (x : I → M.toStarSubalgebra) (hx : ∀ i, υ.trace (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧
      (υ.trace (coordinateInclusion hNM q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q)‖ ^ 2 <
          δ * (υ.trace (coordinateInclusion hNM q)).re := by
  choose T hT using fun n => exists_source_matrix_stage υ hNM hfactor hdiff
    (n + 1) (Nat.succ_pos n)
  exact exists_source_small_projection υ hNM hfactor hdiff hirr T
    (fun n => ⟨n, by rw [hT]; exact Nat.lt_succ_self n⟩) x hx hδ hη

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInclusionQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative local quantization in two abstract von Neumann algebras, through
one faithful normal representation of their given inclusion. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →⋆ₐ[ℂ] B} {τ : B →ₚ[ℂ] ℂ}

namespace TracialInclusionModel
variable (F : TracialInclusionModel φ τ)

include F in
omit [PartialOrder A] [StarOrderedRing A] in
/-- A centered ambient family has an arbitrarily small compression by a
nonzero projection in the original source algebra. -/
theorem exists_small_source_compression [Nontrivial A]
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1)
    {I : Type*} [Fintype I] (x : I → B) (hx : ∀ i, τ (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ (τ (φ q)).re < η ∧
      ∀ i, ‖τ.toPreGNS (φ q * x i * φ q)‖ ^ 2 < δ * (τ (φ q)).re := by
  let : Nontrivial F.N.toStarSubalgebra := nontrivial_of_ne
    (F.sourceEquiv 0) (F.sourceEquiv 1)
    (fun h => zero_ne_one (F.sourceEquiv.injective h))
  obtain ⟨q, hq, hq0, ht, hc⟩ := exists_source_small_projection_of_diffuse
    F.representation F.le (F.source_factor hfactor) (F.source_diffuse hdiff)
    (F.source_irreducible hirr) (fun i => F.ambientEquiv (x i))
    (fun i => (F.trace_eq (x i)).trans (hx i)) hδ hη
  let r := F.sourceEquiv.symm q
  have he : F.ambientEquiv (φ r) = coordinateInclusion F.le q := by
    rw [← F.compatible, F.sourceEquiv.apply_symm_apply]
  have htrace : τ (φ r) = F.representation.trace (coordinateInclusion F.le q) := by
    rw [← F.trace_eq, he]
  refine ⟨r, hq.map F.sourceEquiv.symm, ?_, by rwa [htrace], ?_⟩
  · intro hr
    apply hq0
    have hh := congrArg F.sourceEquiv hr
    simpa only [r, F.sourceEquiv.apply_symm_apply, map_zero] using hh
  · intro i
    rw [htrace]
    have hn := preGNS_norm_map_eq τ
      (vectorPositiveFunctional F.M F.representation.vector)
      F.ambientEquiv.toStarAlgHom F.trace_eq (φ r * x i * φ r)
    change ‖(vectorPositiveFunctional F.M F.representation.vector).toPreGNS
      (F.ambientEquiv (φ r * x i * φ r))‖ = _ at hn
    rw [map_mul F.ambientEquiv, map_mul F.ambientEquiv, he] at hn
    rw [← hn]
    exact hc i

end TracialInclusionModel

/-- Apply relative quantization directly to the supplied normal traces. -/
theorem exists_relative_compression_of_predual
    [Nontrivial A]
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (eA : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (eB : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] B)
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hnA : BoundedHochschild.TraceInPredual eA τA)
    (hnB : BoundedHochschild.TraceInPredual eB τB)
    (h1B : τB 1 = 1) (htrB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (ψ : A →⋆ₐ[ℂ] B) (hi : Function.Injective ψ)
    (ht : ∀ a, τB (ψ a) = τA a)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, ψ a * c = c * ψ a) → ∃ z : ℂ, c = z • 1)
    {I : Type*} [Fintype I] (x : I → B) (hx : ∀ i, τB (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ (τB (ψ q)).re < η ∧
      ∀ i, ‖τB.toPreGNS (ψ q * x i * ψ q)‖ ^ 2 < δ * (τB (ψ q)).re := by
  obtain ⟨F⟩ := exists_tracialInclusionModel eA eB τA τB hnA hnB h1B htrB hfB ψ hi ht
  exact F.exists_small_source_compression hfactor hdiff hirr x hx hδ hη

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

local instance sourceCornerAmbientClosed_r2ea6a4_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.sourceCornerSourceClosed
include υ in
/-- Corner irreducibility retains the given source inclusion. -/
theorem source_corner_irreducible
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c =
        c * coordinateInclusion hNM a) → ∃ z : ℂ, c = z • 1)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) :
    ∀ c : Corner (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM)),
      (∀ a : Corner p hp, sourceCornerHom (coordinateInclusion hNM) p hp a * c =
        c * sourceCornerHom (coordinateInclusion hNM) p hp a) → ∃ z : ℂ, c = z • 1 := by
  intro c hc
  let P := insideAlgebra (M := M) (P := N)
  have hi : ∀ b : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra) * b = b * (a : M.toStarSubalgebra)) →
      ∃ z : ℂ, b = z • 1 := by
    intro b hb
    exact hirr b (fun a => hb ⟨coordinateInclusion hNM a, a.property⟩)
  have hcomm (a : P) : Commute (c : M.toStarSubalgebra)
      (coordinateInclusion hNM p * (a : M.toStarSubalgebra) * coordinateInclusion hNM p) := by
    let b : N.toStarSubalgebra := ⟨a.val.val, a.property⟩
    let d : Corner p hp := ⟨p * b * p, compress_mem_corner hp b⟩
    have hh := congrArg
      (fun x : Corner (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM)) =>
        (x : M.toStarSubalgebra)) (hc d)
    change (coordinateInclusion hNM p * (a : M.toStarSubalgebra) * coordinateInclusion hNM p) *
      (c : M.toStarSubalgebra) = (c : M.toStarSubalgebra) *
      (coordinateInclusion hNM p * (a : M.toStarSubalgebra) * coordinateInclusion hNM p) at hh
    exact hh.symm
  obtain ⟨z, hz⟩ := corner_commutant_scalar υ P hi
    ⟨coordinateInclusion hNM p, hp.map (coordinateInclusion hNM)⟩ (c : M.toStarSubalgebra)
    c.property.1 c.property.2 hcomm
  exact ⟨z, Subtype.ext hz⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceMomentConstruction
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maximal partial unitaries for ambient moments, ordered inside the source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison HochschildPatching BoundedHochschild
open Filter Topology
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

attribute [local instance] OAI.KadisonSimilarity.momentSourceClosed
/-- Ambient moment bounds persist under trace-norm limits in the source. -/
theorem source_momentBound_limit {I : Type*} [Fintype I]
    (F : I → M.toStarSubalgebra) {K N : ℕ} {b : ℝ → ℝ}
    {v : ℕ → PartialUnitary R.toStarSubalgebra} {w : PartialUnitary R.toStarSubalgebra}
    (h : GNSTendsto (vectorPositiveFunctional R υ.vector)
      (fun n => (v n : R.toStarSubalgebra)) atTop (w : R.toStarSubalgebra))
    (hb : ContinuousAt b ((υ.trace (coordinateInclusion hRM w.support)).re))
    (hv : ∀ n, MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N) b
      (SourcePartialUnitary.map (coordinateInclusion hRM) (v n))) :
    MomentBound F (vectorPositiveFunctional M υ.vector) (K := K) (N := N) b
      (SourcePartialUnitary.map (coordinateInclusion hRM) w) := by
  let φ := coordinateInclusion hRM
  let τ := vectorPositiveFunctional M υ.vector
  have ht : GNSTendsto τ
      (fun n => (SourcePartialUnitary.map φ (v n) : M.toStarSubalgebra)) atTop
      (SourcePartialUnitary.map φ w : M.toStarSubalgebra) := source_gns_tendsto υ hRM h
  apply momentBound_limit F τ υ.trace_mul_comm
    (v := fun n => SourcePartialUnitary.map φ (v n)) (w := SourcePartialUnitary.map φ w)
    υ.trace_one ht
  · rw [SourcePartialUnitary.support_map]
    exact hb
  · exact hv

end KadisonSimilarity

end

end OAI
end


