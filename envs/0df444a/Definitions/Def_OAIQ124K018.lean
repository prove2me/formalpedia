-- Prove2me | Definitions.Def_OAIQ124K018
-- name    : OAIQ124K018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:01:20.258322+00:00
-- url     : https://prove2.me/theorems/cded41e0-ee54-4939-9077-9b317d6ee2e7
-- title:
--   Definitions bundle OAIQ124K018 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 10 definitions and 27 theorems. The definitions and types are `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionEquiv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionMap`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.toImage`, `OAI.KLInvariance.TitsSpace.bottCoordinateLift`, `OAI.KLInvariance.TitsSpace.bottImageSheaf`, `OAI.KLInvariance.TitsSpace.bottIntervalExtension`, `OAI.KLInvariance.TitsSpace.bottPolynomialSheaf`, `OAI.KLInvariance.TitsSpace.bottSection`, `OAI.KLInvariance.TitsSpace.bottStalkDualToSupport`, `OAI.KLInvariance.TitsSpace.bottTopPolynomialEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K012`, `OAIQ124K013`, `OAIQ124K014` and `OAIQ124K015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K019`, `OAIQ124K020` and `OAIQ124K021`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K012
import Definitions.Def_OAIQ124K013
import Definitions.Def_OAIQ124K014
import Definitions.Def_OAIQ124K015

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottHeadPairAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottHeadPairModule _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.bottStalkFinite _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite

end
end KLInvariance.FrobeniusDuality

end


section

/-! Integral weight support and orthogonality for the actual tensor module.
These are the vertex support statements behind the section pairing, not an
identification of the minimal BMP sheaf or its character. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidableEqBottIndex
theorem bott_weight_eigen (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : m ∈ bottWeightSupported cs l x) (a : SymmetricCoefficient (M := M)) :
    bottSamelsonRight cs l a m = coefficientAction cs x a • m := by
  apply bottEvaluation_injective cs l
  funext e
  change bottEvaluation cs l e (bottSamelsonRight cs l a m) =
    bottEvaluation cs l e (coefficientAction cs x a • m)
  erw [bottEvaluation_right,map_smul]
  change _ = coefficientAction cs x a * bottEvaluation cs l e m
  by_cases he : bottWeight cs l e = x
  · rw [he]
  · rw [hm e he,mul_zero,mul_zero]

 theorem bott_eigen_supported (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : ∀ a : SymmetricCoefficient (M := M),
      bottSamelsonRight cs l a m = coefficientAction cs x a • m) :
    m ∈ bottWeightSupported cs l x := by
  intro e he
  obtain ⟨a,ha⟩ := coefficientAction_separates cs he
  have h := congrArg (bottEvaluation cs l e) (hm a)
  erw [bottEvaluation_right,map_smul] at h
  change coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e m =
    coefficientAction cs x a * bottEvaluation cs l e m at h
  have hh : (coefficientAction cs (bottWeight cs l e) a-coefficientAction cs x a) *
      bottEvaluation cs l e m = 0 := by rw [sub_mul,h,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha)

 theorem bott_distinct_weight_orthogonal (l : List I) {x y : W} (hxy : x ≠ y)
    {m n : BottSamelsonModule cs l} (hm : m ∈ bottWeightSupported cs l x)
    (hn : n ∈ bottWeightSupported cs l y) : bottSamelsonDuality cs l m n = 0 := by
  obtain ⟨a,ha⟩ := coefficientAction_separates cs hxy
  have h := bottSamelson_balanced cs l a m n
  rw [bott_weight_eigen cs l x hm,bott_weight_eigen cs l y hn] at h
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h
  have he : (coefficientAction cs x a-coefficientAction cs y a) *
      bottSamelsonDuality cs l m n = 0 := by rw [sub_mul,h,sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha)

 def bottCoordinateLift (l : List I) (e : BottIndex l) : BottSamelsonModule cs l := by
  classical
  exact (bottEvaluation_contains_scaled_coordinates cs l (Pi.single e 1)).choose

 theorem bottCoordinateLift_eval (l : List I) (e j : BottIndex l) :
    bottEvaluation cs l j (bottCoordinateLift cs l e) =
      bottCoordinateDenominator cs l * (Pi.single e 1 : BottIndex l → SymmetricCoefficient (M := M)) j := by
  classical
  exact (bottEvaluation_contains_scaled_coordinates cs l (Pi.single e 1)).choose_spec j

 theorem bottCoordinateLift_supported (l : List I) (e : BottIndex l) :
    bottCoordinateLift cs l e ∈ bottWeightSupported cs l (bottWeight cs l e) := by
  intro j hj
  rw [bottCoordinateLift_eval]
  have hje : j ≠ e := fun h => hj (congrArg (bottWeight cs l) h)
  rw [Pi.single_eq_of_ne hje, mul_zero]

 theorem bottCoordinateExpansion (l : List I) (m : BottSamelsonModule cs l) :
    bottCoordinateDenominator cs l • m =
      ∑ e : BottIndex l, bottEvaluation cs l e m • bottCoordinateLift cs l e := by
  classical
  apply bottEvaluation_injective cs l
  funext j
  simp only [map_smul,map_sum,bottCoordinateLift_eval,smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same,mul_one,mul_comm]
  · intro e _ hej
    rw [Pi.single_eq_of_ne (Ne.symm hej),mul_zero,mul_zero]
  · simp

end
end KLInvariance.TitsSpace

end


section

/-! The actual tensor word's integral weight-support lattice is the dual of
its integral projected stalk lattice. This is not merely a fraction-field
isomorphism. It still does NOT identify BMP sections with an indecomposable
summand of the tensor word, or prove the character theorem. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bott_annihilates_supported (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : ∀ n : BottSamelsonModule cs l, bottWeightProjection cs l x n=0 →
      bottSamelsonDuality cs l m n=0) : m ∈ bottWeightSupported cs l x := by
  apply bott_eigen_supported cs l x
  intro a
  apply (bottSamelsonDuality cs l).injective
  apply LinearMap.ext
  intro n
  have hn : bottWeightProjection cs l x
      (bottSamelsonRight cs l a n - coefficientAction cs x a • n)=0 := by
    apply (bottWeightProjection_eq_zero cs l x _).mpr
    intro e he
    erw [map_sub,bottEvaluation_right,map_smul]
    change coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e n -
      coefficientAction cs x a * bottEvaluation cs l e n=0
    rw [he,sub_self]
  have hh := hm _ hn
  simp only [map_sub,map_smul,smul_eq_mul] at hh
  rw [bottSamelson_balanced]
  change bottSamelsonDuality cs l m (bottSamelsonRight cs l a n) =
    (bottSamelsonDuality cs l (coefficientAction cs x a • m)) n
  rw [map_smul,LinearMap.smul_apply,smul_eq_mul]
  exact sub_eq_zero.mp hh

 def bottStalkDualToSupport (l : List I) (x : W) :
    Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) →ₗ[SymmetricCoefficient (M := M)]
      bottWeightSupported cs l x :=
  ((bottSamelsonDuality cs l).symm.toLinearMap.comp
    (bottStalkProjection cs l x).dualMap).codRestrict (bottWeightSupported cs l x) (by
    intro lam
    apply bott_annihilates_supported cs l x
    intro n hn
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply]
    change lam (bottStalkProjection cs l x n)=0
    rw [(bottStalkProjection_eq_zero cs l x n).mpr hn,map_zero])

end
end KLInvariance.TitsSpace

end


section

/-! The actual integral two-vertex projection sheaf of a tensor
Bott--Samelson module. This is the localization-functor construction, not
an assumed BMP sheaf. Surjectivity onto ALL sections, flabbiness, free stalks,
and the indecomposable normalization remain separate obligations. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSection (l : List I) (u b : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] (bottProjectionSheaf cs l u b).sections Set.univ where
  toFun m := ⟨fun x => bottStalkProjection cs l x.val m,by
    intro e _ _
    exact PairProjection.compatible _ _ m⟩
  map_add' := by
    intro m n
    apply Subtype.ext
    funext x
    exact map_add (bottStalkProjection cs l x.val) m n
  map_smul' := by
    intro r m
    apply Subtype.ext
    funext x
    exact map_smul (bottStalkProjection cs l x.val) r m

 theorem bottProjectionSheaf_generated (l : List I) (u b : W) :
    (bottProjectionSheaf cs l u b).Generated := by
  intro x v
  obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val v
  exact ⟨(bottSection cs l u b m).val,(bottSection cs l u b m).property,hm⟩

 theorem bottProjectionSheaf_lower_surjective (l : List I) (u b : W) (e : Edge cs u b) :
    Function.Surjective ((bottProjectionSheaf cs l u b).lower e) :=
  PairProjection.lower_surjective _ _ (bottStalkProjection_surjective cs l _)

 theorem bottSection_injective (l : List I) (hl : cs.IsReduced l) :
    Function.Injective (bottSection cs l 1 (cs.wordProd l)) := by
  intro m n h
  apply bottEvaluation_injective cs l
  funext e
  let x : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hh := congrArg (fun z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    z.val x) h
  exact congrFun (congrArg Subtype.val hh) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! Genuine word stalk normalization and identification with the honest
Hecke word. This does not identify the indecomposable BMP character with KL. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_7
def bottTopPolynomialEquiv (l : List I) (hl : cs.IsReduced l) :
    bottStalk cs l (cs.wordProd l) ≃ₗ[ℝ] MvPolynomial σ ℝ :=
  ((bottTopStalkEquiv cs l hl).restrictScalars ℝ).trans
    (SymmetricAlgebra.equivMvPolynomial basis).toLinearEquiv

end
end KLInvariance.TitsSpace

end


section

/-! Projectivity on reflection-stable upper sets, via an ACTUAL tensor
splitting rather than an asserted reflexivity of a projected lattice. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ProjectiveRange ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottHeadLocalPair_eq_iff (i : I) (l : List I) (x : W)
    (m n : BottSamelsonModule cs (i::l)) :
    bottStalkProjection cs (i::l) x m=bottStalkProjection cs (i::l) x n ↔
      bottHeadLocalPair cs i l x m=bottHeadLocalPair cs i l x n :=
  maps_eq_iff_of_zero_iff _ _ (bottHeadLocalPair_zero_iff cs i l x) m n

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional flabbiness of the actual integral tensor-word projection
sheaf, obtained from projectivity of every upper-coordinate image. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSetProjection_nil_injective (U : Set W) (hU : (1 : W)∈U) :
    Function.Injective (bottSetProjection cs [] U) := by
  intro m n h
  apply bottEvaluation_injective cs []
  funext e
  exact congrArg (fun z : bottSetImage cs [] U => (z.val ⟨1,hU⟩).val ⟨e,rfl⟩) h

 theorem bottSetImage_nil_subsingleton (U : Set W) (hU : (1 : W)∉U) :
    Subsingleton (bottSetImage cs [] U) := by
  constructor
  intro p q
  apply Subtype.ext
  funext x
  have hx : x.val≠1 := fun h => hU (h ▸ x.property)
  let := bottStalk_nil_subsingleton cs x.val hx
  exact Subsingleton.elim _ _

end
end KLInvariance.TitsSpace

end


section

/-! Flabbiness of the genuine interval word sheaf; the extension outside the
finite support is zero, not an extra assumption on the source interval. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottIntervalExtension (l : List I) (U : Set (Interval cs 1 (cs.wordProd l)))
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (x : intervalUpperClosure cs (cs.wordProd l) U) : bottStalk cs l x.val := by
  classical
  exact if h : BruhatLE cs x.val (cs.wordProd l) then f ⟨x.val,one_bruhat cs x.val,h⟩ else 0

 theorem bottIntervalExtension_apply (l : List I) (U : Set (Interval cs 1 (cs.wordProd l)))
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (x : Interval cs 1 (cs.wordProd l)) (hx : x.val∈intervalUpperClosure cs (cs.wordProd l) U) :
    bottIntervalExtension cs l U f ⟨x.val,hx⟩=f x := by
  classical
  dsimp only [bottIntervalExtension]
  exact dite_eq_left x.property.2

 theorem bottIntervalExtension_compatible (l : List I) (hl : cs.IsReduced l)
    (U : Set (Interval cs 1 (cs.wordProd l))) (hU : IsUpperSet U)
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (hf : (bottProjectionSheaf cs l 1 (cs.wordProd l)).CompatibleOn U f) :
    BottCompatible cs l (intervalUpperClosure cs (cs.wordProd l) U) (bottIntervalExtension cs l U f) := by
  intro x y hx hy hxy
  by_cases hyb : BruhatLE cs y (cs.wordProd l)
  · have hxb : BruhatLE cs x (cs.wordProd l) := bruhat_trans cs (.single hxy) hyb
    let xx : Interval cs 1 (cs.wordProd l) := ⟨x,one_bruhat cs x,hxb⟩
    let yy : Interval cs 1 (cs.wordProd l) := ⟨y,one_bruhat cs y,hyb⟩
    let e : Edge cs 1 (cs.wordProd l) := ⟨(xx,yy),hxy⟩
    have hh := hf e (intervalUpperClosure_member cs _ U hU x hx hxb)
      (intervalUpperClosure_member cs _ U hU y hy hyb)
    obtain ⟨m,hm,hn⟩ := (PairProjection.compatible_iff _ _ _ _).mp hh
    exact ⟨m,hm.trans (bottIntervalExtension_apply cs l U f xx hx).symm,
      hn.trans (bottIntervalExtension_apply cs l U f yy hy).symm⟩
  · let := bottStalk_subsingleton_of_not_bruhat cs l hl y hyb
    obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x (bottIntervalExtension cs l U f ⟨x,hx⟩)
    exact ⟨m,hm,Subsingleton.elim _ _⟩

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

namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPairing_dualToSupport (l : List I) (x : W)
    (lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (m : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l (bottStalkDualToSupport cs l x lam).val m =
      lam (bottStalkProjection cs l x m) := by
  change bottSamelsonDuality cs l
    ((bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam)) m = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end
end KLInvariance.TitsSpace

end


section

/-! The actual word adjoint preserves homogeneity. Projection kernels are
annihilators of the actual supported lattices, integrally, with no localization
or freeness assumption on the projection lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottAdjoint_homogeneous
    {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
    (l : List I) (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ n m, m ∈ bottPiece cs basis l n → f m ∈ bottPiece cs basis l n)
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottAdjoint cs l f m ∈ bottPiece cs basis l n :=
  adjoint_homogeneous (symmetricGrading basis) (bottPiece cs basis l)
    (bottSamelsonDuality cs l) l.length
    (fun _ _ _ _ h1 h2 => bottDuality_homogeneous cs basis l h1 h2) f hf n m hm

end
end KLInvariance.TitsSpace

end


section

/-! Integral realization of tensor words as ALL sections of their actual
pair-projection sheaf. This assertion alone is not a BMP summand theorem,
flabbiness/standard-filtration theorem, or EW character theorem. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottVertexProjection_injective (l : List I) (hl : cs.IsReduced l) :
    Function.Injective (bottVertexProjection cs l 1 (cs.wordProd l)) := by
  intro m n h
  apply bottSection_injective cs l hl
  exact Subtype.ext h

 theorem bottVertexProjection_scaled (l : List I) (hl : cs.IsReduced l)
    (z : ∀ x : Interval cs 1 (cs.wordProd l), bottStalk cs l x.val) :
    bottCoordinateDenominator cs l • z ∈
      LinearMap.range (bottVertexProjection cs l 1 (cs.wordProd l)) := by
  let c (e : BottIndex l) : SymmetricCoefficient (M := M) :=
    (z ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩).val ⟨e,rfl⟩
  obtain ⟨m,hm⟩ := bottEvaluation_contains_scaled_coordinates cs l c
  refine ⟨m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  exact hm e


 theorem bottSection_pair_lift (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (x y : Interval cs u b) (t : W) (ht : cs.IsReflection t) (he : t*x.val=y.val) :
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x.val m=s.val x ∧ bottStalkProjection cs l y.val m=s.val y := by
  have he' : t*y.val=x.val := by
    rw [← he,← mul_assoc,ht.mul_self,one_mul]
  have hne : cs.length y.val ≠ cs.length x.val := by
    rw [← he]
    exact ht.length_mul_right_ne x.val
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let e : Edge cs u b := ⟨(y,x),hlt,⟨t,ht,he'.symm⟩⟩
    have hs := s.property e (Set.mem_univ _) (Set.mem_univ _)
    obtain ⟨m,hm,hn⟩ := (PairProjection.compatible_iff _ _ _ _).mp hs
    exact ⟨m,hn,hm⟩
  · let e : Edge cs u b := ⟨(x,y),hlt,⟨t,ht,he.symm⟩⟩
    have hs := s.property e (Set.mem_univ _) (Set.mem_univ _)
    exact (PairProjection.compatible_iff _ _ _ _).mp hs

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

 theorem bottPiece_iff_stalks (l : List I) (hl : cs.IsReduced l) (n : ℤ)
    (m : BottSamelsonModule cs l) : m ∈ bottPiece cs basis l n ↔
      ∀ x : Interval cs 1 (cs.wordProd l),
        bottStalkProjection cs l x.val m ∈ bottStalkPiece cs basis l x.val n := by
  constructor
  · intro hm x
    exact bottStalkProjection_homogeneous cs basis l x.val n m hm
  · intro hm
    have he : component (bottPiece cs basis l) n m=m := by
      apply bottVertexProjection_injective cs l hl
      funext x
      have hh := map_component (bottPiece cs basis l) (bottStalkPiece cs basis l x.val)
        (bottStalkProjection cs l x.val) 0 (by
          simpa only [add_zero] using bottStalkProjection_homogeneous cs basis l x.val) n m
      rw [sub_zero,show component (bottStalkPiece cs basis l x.val) n
        (bottStalkProjection cs l x.val m)=bottStalkProjection cs l x.val m from
        DirectSum.decompose_of_mem_same _ (hm x)] at hh
      exact hh.symm
    rw [← he]
    exact (DirectSum.decompose (bottPiece cs basis l) m n).property

end
end KLInvariance.TitsSpace

end


section

/-! All integral sections of an idempotent image sheaf are the image of the
actual section projector; this is stronger than equality over the fraction
field and requires the actual idempotence, not merely pointwise surjectivity. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem Hom.imageSection_fixed (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) (f : h.image.forget.sections Ω) :
    h.sectionMap Ω (h.imageInclusion.sectionMap Ω f)=h.imageInclusion.sectionMap Ω f := by
  apply Subtype.ext
  funext x
  obtain ⟨v,hv'⟩ := (f.val x).property
  change (h.vertex x).map (f.val x).val=(f.val x).val
  rw [← hv',hv]

 def Hom.imageSectionMap (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : h.image.forget.sections Ω →ₗ[A] LinearMap.range (h.sectionMap Ω) :=
  (h.imageInclusion.sectionMap Ω).codRestrict _ (fun f =>
    ⟨h.imageInclusion.sectionMap Ω f,h.imageSection_fixed hv Ω f⟩)

 theorem Hom.imageSectionMap_bijective (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : Function.Bijective (h.imageSectionMap hv Ω) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val (congrArg Subtype.val hfg)) x
  · rintro ⟨s,m,rfl⟩
    refine ⟨h.imageProjection.sectionMap Ω m,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

 def Hom.imageSectionEquiv (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : h.image.forget.sections Ω ≃ₗ[A] LinearMap.range (h.sectionMap Ω) :=
  LinearEquiv.ofBijective (h.imageSectionMap hv Ω) (h.imageSectionMap_bijective hv Ω)

end
end KLInvariance.MomentGraph.GradedSheaf

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

 def bottImageSheaf : GradedSheaf (𝓐 := symmetricGrading basis)
    (graph cs 1 (cs.wordProd l)) := by
  letI := symmetricCoefficientNoetherian basis
  exact h.image

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

 def SplitIn.toImage : Hom B s.projector.image := s.projector.imageProjection.comp s.inclusion

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The actual reduced word's top stalk is A in degree zero, integrally and
in BOTH grading directions. This is the normalization needed to start a BMP
summand construction, not a claim about the other stalks. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottTopInvHom_top (s : bottStalk cs l (cs.wordProd l)) :
    (bottTopInvHom cs basis l hl).map ((bottTopHom cs basis l hl).map s)=s :=
  (bottTopStalkEquiv cs l hl).symm_apply_apply s

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

include hl in
 theorem bottBoundarySplit_top_fixed (v : bottStalk cs l (cs.wordProd l)) :
    (s.projector.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map v=v := by
  exact ModuleData.split_reverse_of_unit (symmetricGrading_negative basis) B.top
    (bottTopHom cs basis l hl) (bottTopInvHom cs basis l hl)
    (bottTopInvHom_top cs basis l hl)
    (s.inclusion.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (s.projection.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (s.vertex_split ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) v

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

 def bottPolynomialSheaf (l : List I) (u b : W) :
    GradedSheaf (𝓐 := polynomialGrading ℝ σ) (graph cs u b) :=
  GradedSheaf.coefficientChange (SymmetricAlgebra.equivMvPolynomial basis)
    (mem_symmetricGrading basis) (bottGradedProjectionSheaf cs basis l u b)

 theorem bottPolynomialSheaf_generated (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).forget.Generated :=
  GradedSheaf.coefficientChange_generated _ _ _ (bottProjectionSheaf_generated cs l u b)

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

 theorem bottSupported_of_stalkSupport (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : ∀ y : Interval cs 1 (cs.wordProd l), y≠x → bottStalkProjection cs l y.val m=0) :
    m∈bottWeightSupported cs l x.val := by
  intro e he
  let y : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hy : y≠x := fun h => he (congrArg Subtype.val h)
  exact congrFun (congrArg Subtype.val (hm y hy)) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace

end


end OAI
end


