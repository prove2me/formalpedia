-- Prove2me | Definitions.Def_OAIQ124K023
-- name    : OAIQ124K023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:51:52.19715+00:00
-- url     : https://prove2.me/theorems/159aa1fa-8b82-4db9-97ea-812b5ab63d92
-- title:
--   Definitions bundle OAIQ124K023 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 17 definitions, 1 instance and 30 theorems. The definitions and types are `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.imageSectionEquiv`, `OAI.KLInvariance.TitsSpace.bottAdjointImageEquivDual`, `OAI.KLInvariance.TitsSpace.bottCanonicalAdjointHom`, `OAI.KLInvariance.TitsSpace.bottFreeDuality`, `OAI.KLInvariance.TitsSpace.bottFreeSheaf`, `OAI.KLInvariance.TitsSpace.bottImageSectionWordEquiv`, `OAI.KLInvariance.TitsSpace.bottPolynomialPerfectPairing`, `OAI.KLInvariance.TitsSpace.bottRecognizedPerfectPairing`, `OAI.KLInvariance.TitsSpace.bottSectionDuality`, `OAI.KLInvariance.TitsSpace.bottSplitAdjointEquivDual`, `OAI.KLInvariance.TitsSpace.bottSplitAdjointSplit`, `OAI.KLInvariance.TitsSpace.bottSplitAdjointTopInclusion`, `OAI.KLInvariance.TitsSpace.bottSplitAdjointTopProjection`, `OAI.KLInvariance.TitsSpace.bottSplitLeftWord`, `OAI.KLInvariance.TitsSpace.bottSplitRightWord`, `OAI.KLInvariance.TitsSpace.bottStalkCharacter`, `OAI.KLInvariance.TitsSpace.bottWordPerfectPairing`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_CharacterReciprocity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean), [`KazhdanLusztig_EdgeLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K026`, `OAIQ124K020` and `OAIQ124K021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K024`; the statements `OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both`, `OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution`, `OAI.KLInvariance.TitsSpace.bottStalkCharacter_ascent`, `OAI.KLInvariance.TitsSpace.bottStalkCharacter_descent` and `OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil`; the proofs of `OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution`, `OAI.KLInvariance.TitsSpace.bottStalkCharacter_ascent`, `OAI.KLInvariance.TitsSpace.bottStalkCharacter_descent` and `OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K026
import Definitions.Def_OAIQ124K020
import Definitions.Def_OAIQ124K021

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! The genuine nonnegative polynomial generator character of word stalks,
with its convergent Hilbert-series interpretation. No KL identification is
asserted or included in the definition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance bottPolynomialStalkFree (l : List I) (x : W) :
    Module.Free (MvPolynomial σ ℝ) (bottPolynomialStalkData cs basis l x) :=
  inferInstanceAs (Module.Free (MvPolynomial σ ℝ)
    (CoefficientChange (SymmetricAlgebra.equivMvPolynomial basis) (bottStalk cs l x)))

 def bottStalkCharacter (l : List I) (x : W) : Polynomial ℤ :=
  Graded.character (σ := σ) (bottPolynomialStalkData cs basis l x).piece
    (bottPolynomialStalkData cs basis l x).nonneg

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

/-! Integral perfect balanced self-duality on all sections of the genuine
word projection sheaf. This is the word object, NOT the indecomposable BMP
object. Selection of a BMP summand with the required normalization is not
made or assumed here. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSectionDuality (l : List I) (hl : cs.IsReduced l) :
    (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M))
        ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :=
  (bottSectionEquiv cs l hl).symm.trans
    ((bottSamelsonDuality cs l).trans (bottSectionEquiv cs l hl).symm.dualMap)

 theorem bottSectionDuality_apply (l : List I) (hl : cs.IsReduced l)
    (m n : BottSamelsonModule cs l) :
    bottSectionDuality cs l hl (bottSection cs l 1 (cs.wordProd l) m)
      (bottSection cs l 1 (cs.wordProd l) n) = bottSamelsonDuality cs l m n := by
  change bottSamelsonDuality cs l
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) m))
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) n))= _
  simp only [LinearEquiv.symm_apply_apply]

 theorem bottSection_symmetric (l : List I) (hl : cs.IsReduced l)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl s z=bottSectionDuality cs l hl z s := by
  exact TransportPerfectPairing.symmetric (bottSectionEquiv cs l hl)
    (bottSamelsonDuality cs l) (bottSamelson_symmetric cs l) s z

end
end KLInvariance.TitsSpace

end


section

/-! The word SECTION pairing has precisely the word-length shift in the
actual coordinatewise sheaf grading. It is not an asserted pairing on the
indecomposable BMP boundary sheaf. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottSectionDuality_homogeneous (l : List I) (hl : cs.IsReduced l)
    (i j : ℤ)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hs : ∀ x, s.val x ∈ bottStalkPiece cs basis l x.val i)
    (hz : ∀ x, z.val x ∈ bottStalkPiece cs basis l x.val j) :
    bottSectionDuality cs l hl s z ∈ symmetricGrading basis (i+j-l.length) := by
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  obtain ⟨n,rfl⟩ := bottSection_surjective cs l hl z
  rw [bottSectionDuality_apply]
  exact bottDuality_homogeneous cs basis l ((bottPiece_iff_stalks cs basis l hl i m).mpr hs)
    ((bottPiece_iff_stalks cs basis l hl j n).mpr hz)

end
end KLInvariance.TitsSpace

end


section

/-! Integral graded adjoint WORD projectors. The assumption below is only
that the GIVEN endomorphism is a projector; no existence of a BMP projector
or identification of its image with its adjoint is asserted. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottEndOfSheaf_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : BottSamelsonModule cs l) :
    bottEndOfSheaf cs basis l hl h (bottEndOfSheaf cs basis l hl h m)=
      bottEndOfSheaf cs basis l hl h m := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  simp only [bottEndOfSheaf_coordinates]
  exact hh x _

 theorem bottAdjointSheaf_vertex_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (x : Interval cs 1 (cs.wordProd l))
    (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map
      (((bottAdjointSheaf cs basis l hl h).vertex x).map v)=
      ((bottAdjointSheaf cs basis l hl h).vertex x).map v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  simp only [bottAdjointSheaf_vertex]
  exact congrArg (bottStalkProjection cs l x.val)
    (PerfectAdjoint.adjoint_idempotent (bottSamelsonDuality cs l) _
      (bottEndOfSheaf_idempotent cs basis l hl h hh) m)

 theorem bottAdjointSheaf_edge_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (e : Edge cs 1 (cs.wordProd l))
    (v : (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).edge e) :
    ((bottAdjointSheaf cs basis l hl h).edge e).map
      (((bottAdjointSheaf cs basis l hl h).edge e).map v)=
      ((bottAdjointSheaf cs basis l hl h).edge e).map v := by
  have hs : Function.Surjective
      ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).lower e).map :=
    bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  obtain ⟨m,rfl⟩ := hs v
  simp only [(bottAdjointSheaf cs basis l hl h).lower]
  exact congrArg ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).lower e).map
    (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh _ m)

end
end KLInvariance.TitsSpace

end


section

/-! The actual adjoint IMAGE sheaf has all integral sections dual to those
of the original projector image. This does not identify those two image
sheaves or assert that the word sheaf satisfies the BMP axioms. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottImageSectionWordEquiv
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v) :
    (bottImageSheaf cs basis l h).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)] LinearMap.range (bottEndOfSheaf cs basis l hl h) := by
  letI := symmetricCoefficientNoetherian basis
  exact (h.imageSectionEquiv hh Set.univ).trans
    (ConjugateRange.equiv (bottSectionEquiv cs l hl) (h.sectionMap Set.univ))

 def bottAdjointImageEquivDual
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v) :
    (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M))
        ((bottImageSheaf cs basis l h).forget.sections Set.univ) :=
  (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl h)
      (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh)).trans
    ((LinearEquiv.ofEq _ _ (congrArg LinearMap.range
        (bottEndOfAdjointSheaf cs basis l hl h))).trans
      ((PerfectAdjoint.rangeAdjointEquivDualRange (bottSamelsonDuality cs l)
          (bottEndOfSheaf cs basis l hl h)
          (bottEndOfSheaf_idempotent cs basis l hl h hh)).trans
        (bottImageSectionWordEquiv cs basis l hl h hh).dualMap))

 theorem bottImageSectionWordEquiv_coordinates
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val ((bottImageSectionWordEquiv cs basis l hl h hh m).val)=
      (m.val x).val := by
  let := symmetricCoefficientNoetherian basis
  exact congrArg (fun s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    s.val x) ((bottSectionEquiv cs l hl).apply_symm_apply
      (h.imageInclusion.sectionMap Set.univ m))

 theorem bottImageSectionWordEquiv_homogeneous
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (n : ℤ) (m : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈ ((bottImageSheaf cs basis l h).vertex x).piece n) :
    (bottImageSectionWordEquiv cs basis l hl h hh m).val ∈ bottPiece cs basis l n := by
  apply (bottPiece_iff_stalks cs basis l hl n _).mpr
  intro x
  rw [bottImageSectionWordEquiv_coordinates]
  exact hm x

 theorem bottAdjointImageEquivDual_apply
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ)
    (n : (bottImageSheaf cs basis l h).forget.sections Set.univ) :
    bottAdjointImageEquivDual cs basis l hl h hh m n=bottSamelsonDuality cs l
      (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl h)
        (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh) m).val
      (bottImageSectionWordEquiv cs basis l hl h hh n).val := rfl

 theorem bottAdjointImagePairing_homogeneous
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (i j : ℤ)
    (m : (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ)
    (n : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈
      ((bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).vertex x).piece i)
    (hn : ∀ x, n.val x ∈ ((bottImageSheaf cs basis l h).vertex x).piece j) :
    bottAdjointImageEquivDual cs basis l hl h hh m n ∈ symmetricGrading basis (i+j-(l.length : ℤ)) := by
  rw [bottAdjointImageEquivDual_apply]
  exact bottDuality_homogeneous cs basis l
    (bottImageSectionWordEquiv_homogeneous cs basis l hl _
      (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh) i m hm)
    (bottImageSectionWordEquiv_homogeneous cs basis l hl h hh j n hn)

end
end KLInvariance.TitsSpace

end


section

/-! A specified integral graded sheaf splitting identifies its source with
its literal projector image. No existence of a word/BMP splitting is assumed
outside each explicitly parametric helper. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 theorem SplitIn.imageSection_bijective (Ω : Set V) :
    Function.Bijective (s.imageTo.sectionMap Ω) := by
  constructor
  · intro m n he
    apply Subtype.ext
    funext x
    have hx := congrFun (congrArg Subtype.val he) x
    have hy := congrArg (s.toImage.vertex x).map hx
    exact (s.toImage_imageTo_vertex x (m.val x)).symm.trans
      (hy.trans (s.toImage_imageTo_vertex x (n.val x)))
  · intro m
    refine ⟨s.toImage.sectionMap Ω m,?_⟩
    apply Subtype.ext
    funext x
    exact s.imageTo_toImage_vertex x (m.val x)

 def SplitIn.imageSectionEquiv (Ω : Set V) :
    s.projector.image.forget.sections Ω ≃ₗ[A] B.forget.sections Ω :=
  LinearEquiv.ofBijective (s.imageTo.sectionMap Ω) (s.imageSection_bijective Ω)

 theorem SplitIn.imageSectionEquiv_symm_apply (Ω : Set V) (m : B.forget.sections Ω) :
    (s.imageSectionEquiv Ω).symm m=s.toImage.sectionMap Ω m := by
  apply (s.imageSectionEquiv Ω).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  exact (s.imageTo_toImage_vertex x (m.val x)).symm

 theorem SplitIn.imageSectionEquiv_symm_homogeneous (Ω : Set V) (n : ℤ)
    (m : B.forget.sections Ω) (hm : ∀ x, m.val x ∈ (B.vertex x).piece n) (x : V) :
    ((s.imageSectionEquiv Ω).symm m).val x ∈ (s.projector.image.vertex x).piece n := by
  rw [s.imageSectionEquiv_symm_apply]
  exact (s.toImage.vertex x).graded n (m.val x) (hm x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Correct integral graded duality for a GIVEN word-sheaf summand: the dual
is realized by its ADJOINT image, not identified with the original summand.
The existence and BMP recognition of that summand remain separate. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitAdjointEquivDual :
    (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M)) (B.forget.sections Set.univ) := by
  letI := symmetricCoefficientNoetherian basis
  exact (bottAdjointImageEquivDual cs basis l hl s.projector s.projector_vertex).trans
    (s.imageSectionEquiv Set.univ).symm.dualMap

 theorem bottSplitAdjointPairing_homogeneous
    (i j : ℤ)
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (n : B.forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈ ((bottSplitAdjointSheaf cs basis l hl B s).vertex x).piece i)
    (hn : ∀ x, n.val x ∈ (B.vertex x).piece j) :
    bottSplitAdjointEquivDual cs basis l hl B s m n ∈
      symmetricGrading basis (i+j-(l.length : ℤ)) := by
  let := symmetricCoefficientNoetherian basis
  exact bottAdjointImagePairing_homogeneous cs basis l hl s.projector s.projector_vertex i j m
    ((s.imageSectionEquiv Set.univ).symm n) hm
    (s.imageSectionEquiv_symm_homogeneous Set.univ j n hn)

end
end KLInvariance.TitsSpace

end


section

/-! An actual word-sheaf endomorphism that is the identity at one stalk has
adjoint equal to the identity at that same stalk. In particular, an identity
TOP projector stays normalized on taking the adjoint. This alone does not
supply free stalks, flabbiness, or the BMP character. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottEndOfSheaf_fixed_support (x : Interval cs 1 (cs.wordProd l))
    (hx : ∀ v, (h.vertex x).map v=v)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottWeightSupported cs l x.val) :
    bottEndOfSheaf cs basis l hl h m=m := by
  apply bottEvaluation_injective cs l
  funext e
  by_cases he : bottWeight cs l e=x.val
  · have ho := bottEndOfSheaf_coordinates cs basis l hl h m x
    exact congrFun (congrArg Subtype.val (ho.trans (hx _))) ⟨e,he⟩
  · exact (bottEndOfSheaf_preserves_support cs basis l hl h x m hm e he).trans
      (hm e he).symm

 theorem bottAdjointSheaf_fixed_stalk (x : Interval cs 1 (cs.wordProd l))
    (hx : ∀ v, (h.vertex x).map v=v) (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map v=v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  rw [bottAdjointSheaf_vertex]
  have hz : bottStalkProjection cs l x.val
      (bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) m-m)=0 := by
    apply (bott_projection_zero_iff_annihilates_support cs l x.val _).mpr
    intro z
    change bottSamelsonDuality cs l z.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
        (bottEndOfSheaf cs basis l hl h) m-m)=0
    rw [map_sub,PerfectAdjoint.symmetric_pairing _ (bottSamelson_symmetric cs l)]
    rw [bottEndOfSheaf_fixed_support cs basis l hl h x hx z.val z.property,sub_self]
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

/-! The projector of any actual normalized BMP splitting into the reduced
word, and its integral adjoint, are both the identity at the top. The splitting
is not asserted to exist; word BMP recognition and character remain separate. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (α : Edge cs 1 (cs.wordProd l) → SymmetricCoefficient (M := M))
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) α
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottBoundarySplitAdjoint_top_fixed (v : bottStalk cs l (cs.wordProd l)) :
    ((bottAdjointSheaf cs basis l hl s.projector).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map v=v :=
  bottAdjointSheaf_fixed_stalk cs basis l hl s.projector
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩
    (bottBoundarySplit_top_fixed cs basis l hl α B s) v

end
end KLInvariance.TitsSpace

end


section

/-! Positive triangular decomposition of the honest word's character into
actual BMP stalk characters. The KL identification is not assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPolynomialSheaf_free (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).FreeStalks :=
  GradedSheaf.coefficientChange_free _ _ _ (fun x => bottStalkFree cs l x.val)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_supported_annihilates (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) (m n : BottSamelsonModule cs l)
    (hm : ∀ y : Interval cs 1 (cs.wordProd l), y≠x → bottStalkProjection cs l y.val m=0)
    (hn : bottStalkProjection cs l x.val n=0) : bottSamelsonDuality cs l m n=0 :=
  bott_supported_annihilates cs l x.val (bottSupported_of_stalkSupport cs l hl x m hm) n
    (congrArg Subtype.val hn)

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Genuine word costalk character from the integral word pairing, transported
along the fixed symmetric-algebra coordinate isomorphism. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottSection_left_orthogonal (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (m n : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hm : ∀ y, y≠x → m.val y=0) (hn : n.val x=0) :
    bottSectionDuality cs l hl m n=0 := by
  obtain ⟨a,rfl⟩ := bottSection_surjective cs l hl m
  obtain ⟨b,rfl⟩ := bottSection_surjective cs l hl n
  rw [bottSectionDuality_apply]
  exact bottStalk_supported_annihilates cs l hl x a b hm hn

 theorem bottSection_right_orthogonal (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (m n : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hm : m.val x=0) (hn : ∀ y, y≠x → n.val y=0) :
    bottSectionDuality cs l hl m n=0 := by
  rw [bottSection_symmetric]
  exact bottSection_left_orthogonal cs l hl x n m hn hm

 def bottWordPerfectPairing (l : List I) (hl : cs.IsReduced l) :
    GradedSheaf.PerfectPairing (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (l.length : ℤ) where
  pairing := bottSectionDuality cs l hl
  homogeneous := bottSectionDuality_homogeneous cs basis l hl
  left_orthogonal := bottSection_left_orthogonal cs l hl
  right_orthogonal := bottSection_right_orthogonal cs l hl

 def bottPolynomialPerfectPairing (l : List I) (hl : cs.IsReduced l) :
    GradedSheaf.PerfectPairing (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)) (l.length : ℤ) :=
  (bottWordPerfectPairing cs basis l hl).coefficientChange (SymmetricAlgebra.equivMvPolynomial basis)
    (mem_symmetricGrading basis)

 def bottFreeSheaf (l : List I) : FreeSheaf cs 1 (cs.wordProd l) basis where
  sheaf := bottPolynomialSheaf cs basis l 1 (cs.wordProd l)
  free := bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l)
  quotient := bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l)
  generated := bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l)

 attribute [local instance] OAI.KLInvariance.TitsSpace.finiteEdges
attribute [local instance] OAI.KLInvariance.TitsSpace.charDecEqA
def bottFreeDuality (l : List I) (hl : cs.IsReduced l) :
    FreeSheaf.SectionDuality cs 1 (cs.wordProd l) basis (bottFreeSheaf cs basis l) :=
  FreeSheaf.dualityOfPairing cs 1 (cs.wordProd l) basis _ (bottPolynomialPerfectPairing cs basis l hl)

 theorem bottKernelFree (l : List I) (hl : cs.IsReduced l) (x : Interval cs 1 (cs.wordProd l)) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)) x) :=
  FreeSheaf.kernel_free cs (cs.wordProd l) basis _ (bottFreeDuality cs basis l hl) x

end
end KLInvariance.TitsSpace

end


section

/-! The actual symmetric-coefficient BMP boundary sheaf is isomorphic to
its integral adjoint image. The splitting is constructed from the word's
proved free-stalk, exact-edge and flabbiness properties. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitAdjointSplit : GradedSheaf.SplitIn
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s)
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)) := by
  let := symmetricCoefficientNoetherian basis
  exact (bottAdjointSheaf cs basis l hl s.projector).imageSplit
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex)
    (bottAdjointSheaf_edge_idempotent cs basis l hl s.projector s.projector_vertex)

 theorem bottSplitAdjoint_free (x : Interval cs 1 (cs.wordProd l)) :
    Module.Free (SymmetricCoefficient (M := M))
      ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex x) := by
  let := symmetricCoefficientNoetherian basis
  let : Module.Free (SymmetricCoefficient (M := M))
      ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).vertex x) :=
    bottStalkFree cs l x.val
  exact (bottSplitAdjointSplit cs basis l hl B s).vertex_free
    (symmetricGrading_negative basis) (symmetricGrading_zero basis) x

 def bottSplitAdjointTopInclusion : ModuleData.Hom
    (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  ((bottSplitAdjointSplit cs basis l hl B s).projection.vertex _).comp
    (bottBoundarySheafTopInclusion cs basis l hl B)

 def bottSplitAdjointTopProjection : ModuleData.Hom
    ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  (bottBoundarySheafTopProjection cs basis l hl B).comp
    ((bottSplitAdjointSplit cs basis l hl B s).inclusion.vertex _)

 theorem bottSplitAdjointTop_split
    (v : B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    (bottSplitAdjointTopProjection cs basis l hl B s).map
      ((bottSplitAdjointTopInclusion cs basis l hl B s).map v)=v := by
  change (bottBoundarySheafTopProjection cs basis l hl B).map
    (((bottAdjointSheaf cs basis l hl s.projector).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v))=v
  exact (congrArg (bottBoundarySheafTopProjection cs basis l hl B).map
    (bottBoundarySplitAdjoint_top_fixed cs basis l hl _ B s
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v))).trans
    (bottBoundarySheafTop_split cs basis l hl B v)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 theorem SplitIn.imageSectionEquiv_symm_coordinates (U : Set V)
    (n : B.forget.sections U) (x : V) :
    (((s.imageSectionEquiv U).symm n).val x).val=(s.inclusion.vertex x).map (n.val x) := by
  rw [s.imageSectionEquiv_symm_apply]
  change (s.inclusion.vertex x).map ((s.projection.vertex x).map
    ((s.inclusion.vertex x).map (n.val x)))=(s.inclusion.vertex x).map (n.val x)
  exact congrArg (s.inclusion.vertex x).map (s.vertex_split x (n.val x))

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The adjoint-summand pairing is the ambient word pairing on its two
honest (generally different) integral sheaf embeddings. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitRightWord (n : B.forget.sections Set.univ) : BottSamelsonModule cs l := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv cs basis l hl s.projector s.projector_vertex
    ((s.imageSectionEquiv Set.univ).symm n)).val

 def bottSplitLeftWord
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ) :
    BottSamelsonModule cs l := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl s.projector)
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex) m).val

 theorem bottSplitRightWord_coordinates (n : B.forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottSplitRightWord cs basis l hl B s n)=
      (s.inclusion.vertex x).map (n.val x) := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv_coordinates cs basis l hl s.projector s.projector_vertex
    ((s.imageSectionEquiv Set.univ).symm n) x).trans
      (s.imageSectionEquiv_symm_coordinates Set.univ n x)

 theorem bottSplitLeftWord_coordinates
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottSplitLeftWord cs basis l hl B s m)=(m.val x).val := by
  let := symmetricCoefficientNoetherian basis
  exact bottImageSectionWordEquiv_coordinates cs basis l hl
    (bottAdjointSheaf cs basis l hl s.projector)
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex) m x

 theorem bottSplitAdjointWord_apply
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (n : B.forget.sections Set.univ) :
    bottSplitAdjointEquivDual cs basis l hl B s m n=
      bottSamelsonDuality cs l (bottSplitLeftWord cs basis l hl B s m)
        (bottSplitRightWord cs basis l hl B s n) := by
  let := symmetricCoefficientNoetherian basis
  exact bottAdjointImageEquivDual_apply cs basis l hl s.projector s.projector_vertex m
    ((s.imageSectionEquiv Set.univ).symm n)

end
end KLInvariance.TitsSpace

end


section

/-! An actual recognition isomorphism to the adjoint image gives the required
perfect pairing. The two ambient embeddings remain distinct. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
  (j : GradedSheaf.Iso B (bottSplitAdjointSheaf cs basis l hl B s))
noncomputable section

 def bottRecognizedPerfectPairing : GradedSheaf.PerfectPairing B (l.length : ℤ) where
  pairing := (j.toIso.sections Set.univ).trans (bottSplitAdjointEquivDual cs basis l hl B s)
  homogeneous i q m n hm hn := bottSplitAdjointPairing_homogeneous cs basis l hl B s i q
    (j.toIso.sections Set.univ m) n (fun x => j.vertex_graded x i _ (hm x)) hn
  left_orthogonal x m n hm hn := by
    change bottSplitAdjointEquivDual cs basis l hl B s (j.toIso.sections Set.univ m) n=0
    rw [bottSplitAdjointWord_apply]
    apply bottStalk_supported_annihilates cs l hl x
    · intro y hy
      rw [bottSplitLeftWord_coordinates]
      change ((j.vertex y (m.val y)).val)=0
      rw [hm y hy,map_zero]
      rfl
    · rw [bottSplitRightWord_coordinates]
      change (s.inclusion.vertex x).map (n.val x)=0
      rw [hn]
      exact (s.inclusion.vertex x).map.map_zero
  right_orthogonal x m n hm hn := by
    change bottSplitAdjointEquivDual cs basis l hl B s (j.toIso.sections Set.univ m) n=0
    rw [bottSplitAdjointWord_apply,bottSamelson_symmetric]
    apply bottStalk_supported_annihilates cs l hl x
    · intro y hy
      rw [bottSplitRightWord_coordinates]
      change (s.inclusion.vertex y).map (n.val y)=0
      rw [hn y hy]
      exact (s.inclusion.vertex y).map.map_zero
    · rw [bottSplitLeftWord_coordinates]
      change ((j.vertex x (m.val x)).val)=0
      rw [hm,map_zero]
      rfl

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section

/-! The CANONICAL map from a normalized BMP summand to its adjoint image is
invertible. Consequently the ambient WORD form restricts perfectly on this
particular summand; no such assertion is made for an arbitrary summand. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottCanonicalAdjointHom : GradedSheaf.Hom B.sheaf
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s) :=
  (bottSplitAdjointSplit cs basis l hl B s).projection.comp s.inclusion

 theorem bottCanonicalAdjointHom_top_bijective : Function.Bijective
    ((bottCanonicalAdjointHom cs basis l hl B s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map := by
  apply s.comparison_bijective (bottSplitAdjointSplit cs basis l hl B s)
  · exact bottBoundarySplit_top_fixed cs basis l hl _ B s
  · exact bottBoundarySplitAdjoint_top_fixed cs basis l hl _ B s

end
end KLInvariance.TitsSpace

end


section

/-! On the normalized BMP summand the canonical adjoint recognition proves,
rather than assumes, perfection of the restricted symmetric word form. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottSplitRightWord_fixed (n : B.sheaf.forget.sections Set.univ) :
    bottEndOfSheaf cs basis l hl s.projector (bottSplitRightWord cs basis l hl B.sheaf s n)=
      bottSplitRightWord cs basis l hl B.sheaf s n := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  rw [bottEndOfSheaf_coordinates,bottSplitRightWord_coordinates]
  change (s.inclusion.vertex x).map
      ((s.projection.vertex x).map ((s.inclusion.vertex x).map (n.val x)))=
    (s.inclusion.vertex x).map (n.val x)
  exact congrArg (s.inclusion.vertex x).map (s.vertex_split x (n.val x))

end
end KLInvariance.TitsSpace

end


end OAI
end


