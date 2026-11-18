-- Prove2me | Definitions.Def_OAIQ368Chrom031
-- name    : OAIQ368Chrom031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:37:48.34307+00:00
-- url     : https://prove2.me/theorems/bfddcb85-aee4-41cb-b080-8cf24f4c9371
-- title:
--   Definitions bundle OAIQ368Chrom031 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 10 definitions and 45 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SplitTree.degreeCutIdeal`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.translationAtB`, `OAI.ElementaryPositivity.RawShuffle.globalCoproduct`, `OAI.ElementaryPositivity.RawShuffle.globalHomogeneousCoproduct`, `OAI.ElementaryPositivity.RawShuffle.globalSplitCoproduct`, `OAI.ElementaryPositivity.RawShuffle.sourceTensorFiltrationIdeal`, `OAI.ElementaryPositivity.RawShuffle.splitCoproductFiltration`, `OAI.ElementaryPositivity.RawShuffle.splitCoproductGrade`, `OAI.ElementaryPositivity.RawShuffle.unitalGradeCoproduct`, `OAI.ElementaryPositivity.RawShuffle.unitalSourceTensorFiltrationIdeal`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Histories_TwoLeafDiagonal`, `Chromatic_Shuffle_BothTaylorB`, `Chromatic_Shuffle_ClearedSeparationB`, `Chromatic_Shuffle_CrossScalar`, `Chromatic_Shuffle_Degree`, `Chromatic_Shuffle_DegreeIdeals`, `Chromatic_Shuffle_FourBraiding`, `Chromatic_Shuffle_GridShapeFiltration`, `Chromatic_Shuffle_LaurentLeading`, `Chromatic_Shuffle_ManyBlockDiagonal`, `Chromatic_Shuffle_PointEvaluation`, `Chromatic_Shuffle_Restriction`, `Chromatic_Shuffle_SeparationCoefficients`, `Chromatic_Shuffle_SignedTensorGradeProduct`, `Chromatic_Shuffle_TensorFiltration`, `Chromatic_Shuffle_UnitalFiltration`, `Chromatic_Shuffle_UnitalGrade`, `Chromatic_Shuffle_UnitalShuffleCoproduct`, `Chromatic_Walls_CenterLineSpecialization`, `Chromatic_Walls_RefinedLaurent`, `Chromatic_Walls_RefinedTensorDetection`.
--
--   **Imports.** It imports the bundles `OAIQ368Chrom028` and `OAIQ368Chrom030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom035` and `OAIQ368Chrom039`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom028
import Definitions.Def_OAIQ368Chrom030

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_BothTaylorB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma bothLeading_relative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    IndependentCenters.plus (bothLeading a c η hc hs p q f)=
      commonRelativeLeading a c η hc hs p q f := by
  apply evalTwo_ext
  intro z w
  change IndependentCenters.eval z w (IndependentCenters.plus _) = _
  rw [IndependentCenters.eval_plus]
  change evalTwo (bothLeading a c η hc hs p q f) (z+w) w = _
  rw [bothLeading_eval,commonRelativeLeading_eval,restrictionB_translation]
  congr 1
  generalize restrictionB a c η hc hs (firstCut d e) f=x
  induction x using OAI.tensorInductionOn with
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,translationB_add]
  | add x y hx hy => simp only [map_add,hx,hy]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma evalRat_extendPolynomial {A D α β : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (f : A →ₐ[ℚ] D) (j : α → β)
    (p : MvPolynomial α A) (v : β → ℚ) :
    evalRat v (extendPolynomial f j p) = f (evalRat (v ∘ j) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [extendPolynomial]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    congr 1
    simp [extendPolynomial,evalRat]

noncomputable def translationAtB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    (T : SplitTree I) → (T.Centers → ℚ) →
      tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T
  | .leaf d, v => translationB a μ d (v ())
  | .node l r, v => TensorProduct.map
      (translationAtB a μ l (v ∘ Sum.inl)) (translationAtB a μ r (v ∘ Sum.inr))

lemma centerTranslation_evalRat (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) (v : T.Centers → ℚ) :
    evalRat v (centerTranslation (quotientFamily a μ) (taylorB a μ) T x) =
      translationAtB a μ T v x := by
  induction T with
  | leaf d =>
    change B a μ d at x
    change evalRat v (Polynomial.toMvPolynomial () (taylorB a μ d x)) = _
    rw [evalRat_toMvPolynomial,taylorB_eval]
    rfl
  | node l r ihl ihr =>
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      erw [centerTranslation_tmul,map_mul,evalRat_extendPolynomial,evalRat_extendPolynomial,ihl,ihr]
      change (translationAtB a μ l (v ∘ Sum.inl) x ⊗ₜ[ℚ] 1) *
        (1 ⊗ₜ[ℚ] translationAtB a μ r (v ∘ Sum.inr) y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma pairRefinement_translationAtB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I)
    (x : tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T))
    (v : Unit ⊕ T.Centers → ℚ) (t : ℚ) :
    translationAtB a (SlopeArithmetic.slope c η) (.node (.node (.leaf d) (.leaf e)) T)
      (relativePoint t v)
      (TensorProduct.map (RawShuffle.restrictionB a c η hc hs (firstCut d e)).toLinearMap
        (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
          tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) x) =
    (pairRelativeRefinement a c η hc hs T
      (translationAtB a (SlopeArithmetic.slope c η) (.node (.leaf (d+e)) T) v x)).eval
        (algebraMap ℚ _ t) := by
  induction x using OAI.tensorInductionOn with
  | tmul g h =>
    let μ := SlopeArithmetic.slope c η
    change translationAtB a μ (.node (.node (.leaf d) (.leaf e)) T) (relativePoint t v)
      ((RawShuffle.restrictionB a c η hc hs (firstCut d e) g) ⊗ₜ[ℚ] h) =
      (pairRelativeRefinement a c η hc hs T
        (translationB a μ (d+e) (v (Sum.inl ())) g ⊗ₜ[ℚ]
          translationAtB a μ T (v ∘ Sum.inr) h)).eval _
    erw [pairRelativeRefinement_eval_tmul a c η hc hs T,
      restrictionB_translation a c η hc hs (firstCut d e)]
    change TensorProduct.map (translationB a μ d (t+v (Sum.inl ())))
        (translationB a μ e (v (Sum.inl ())))
        (RawShuffle.restrictionB a c η hc hs (firstCut d e) g) ⊗ₜ[ℚ]
          translationAtB a μ T (v ∘ Sum.inr) h = _
    congr 1
    generalize RawShuffle.restrictionB a c η hc hs (firstCut d e) g = y
    induction y using OAI.tensorInductionOn with
    | tmul f h =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,translationB_add]
      rfl
    | add y y' hy hy' => simp only [map_add,hy,hy']
  | add x y hx hy =>
    erw [map_add,map_add,map_add,map_add,Polynomial.eval_add]
    exact congrArg₂ (· + ·) hx hy

lemma pairRefinement_centerTranslation (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I)
    (x : tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T)) :
    toRelative (centerTranslation (quotientFamily a (SlopeArithmetic.slope c η))
      (taylorB a (SlopeArithmetic.slope c η)) (.node (.node (.leaf d) (.leaf e)) T)
        (TensorProduct.map (RawShuffle.restrictionB a c η hc hs (firstCut d e)).toLinearMap
          (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
            tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) x)) =
      map (pairRelativeRefinement a c η hc hs T).toRingHom
        (centerTranslation (quotientFamily a (SlopeArithmetic.slope c η))
          (taylorB a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T) x) := by
  let μ := SlopeArithmetic.slope c η
  let U : SplitTree I := .node (.leaf (d+e)) T
  let V : SplitTree I := .node (.node (.leaf d) (.leaf e)) T
  let refine : tensor (quotientFamily a μ) U →ₗ[ℚ] tensor (quotientFamily a μ) V :=
    TensorProduct.map (RawShuffle.restrictionB a c η hc hs (firstCut d e)).toLinearMap
      (LinearMap.id : tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T)
  let F := pairRelativeRefinement a c η hc hs T
  apply eq_of_evalRat
  intro v
  apply polynomial_eq_of_rat_evals
  intro t
  calc
    _ = evalRat (relativePoint t v)
        (centerTranslation (quotientFamily a μ) (taylorB a μ) V (refine x)) :=
      evalRat_toRelative _ v t
    _ = translationAtB a μ V (relativePoint t v) (refine x) :=
      centerTranslation_evalRat a μ V (refine x) (relativePoint t v)
    _ = (F (translationAtB a μ U v x)).eval (algebraMap ℚ _ t) :=
      pairRefinement_translationAtB a c η hc hs T x v t
    _ = (F (evalRat v (centerTranslation (quotientFamily a μ) (taylorB a μ) U x))).eval
        (algebraMap ℚ _ t) := by
      congr 2
      exact (centerTranslation_evalRat a μ U x v).symm
    _ = _ := congrArg (fun p => p.eval (algebraMap ℚ _ t))
      (evalRat_mapAlgHom F (centerTranslation (quotientFamily a μ) (taylorB a μ) U x) v).symm

lemma pairRelativeRefinement_component_coeff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) (s : ℕ) (p q : ℤ) (k : T.Degrees)
    (x : tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T)) :
    (polynomialMapLinear (componentTensor a (SlopeArithmetic.slope c η)
      (.node (.node (.leaf d) (.leaf e)) T) ((p,q),k))
        (pairRelativeRefinement a c η hc hs T x)).coeff s =
      pairRefinementCoefficient a c η hc hs T s p q k x := by
  rw [polynomialMapLinear_coeff]
  induction x using OAI.tensorInductionOn with
  | tmul g h =>
    erw [pairRelativeRefinement,polynomialOnLeft_coeff_tmul]
    rfl
  | add x y hx hy => simp only [map_add,Polynomial.coeff_add,hx,hy]

end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_pairRefinement (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim)) :
    toRelative (centeredRestrictionB a c η hc θ (.node (.node (.leaf d) (.leaf e)) T)
      ⟨⟨hd,he⟩,hT⟩ f) =
      map (pairRelativeRefinement a c η hc (hd.2.trans he.2.symm) T).toRingHom
        (centeredRestrictionB a c η hc θ (.node (.leaf (d+e)) T)
          ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd.1,
            (SlopeArithmetic.slope_add_same c η hc (hd.2.trans he.2.symm)).trans hd.2⟩,hT⟩ f) := by
  simp only [centeredRestrictionB,AlgHom.comp_apply]
  rw [restrictionB_pairRefinement a c η hc θ hd he T hT]
  exact pairRefinement_centerTranslation a c η hc (hd.2.trans he.2.symm) T _

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TwoLeafDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_two_eval (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) (v : Unit ⊕ Unit → ℚ) :
    evalRat v (centeredRestrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f) =
    TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d (v (Sum.inl ())))
      (translationB a (SlopeArithmetic.slope c η) e (v (Sum.inr ())))
      (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e) f) := by
  exact (centerTranslation_evalRat a (SlopeArithmetic.slope c η)
    (.node (.leaf d) (.leaf e)) _ v).trans
    (congrArg (translationAtB a (SlopeArithmetic.slope c η) (.node (.leaf d) (.leaf e)) v)
      (restrictionB_two a c η hc θ hd he f))

lemma twoLeading_eq (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    {d e : I → ℕ} (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ) (p q : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    mapLinear (componentTensor a (SlopeArithmetic.slope c η) (.node (.leaf d) (.leaf e)) (p,q))
      (centeredRestrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f) =
    ofTwo (bothLeading a c η hc (hd.2.trans he.2.symm) p q f) := by
  let μ := SlopeArithmetic.slope c η
  let l : (B a μ d ⊗[ℚ] B a μ e) →ₗ[ℚ] (B a μ d ⊗[ℚ] B a μ e) :=
    TensorProduct.map (componentB a μ d p) (componentB a μ e q)
  change mapLinear l _ = _
  apply eq_of_evalRat (A:=B a μ d ⊗[ℚ] B a μ e)
  intro v
  exact (evalRat_mapLinear l _ v).trans ((congrArg l
    (centeredRestrictionB_two_eval a c η hc θ hd he f v)).trans
    ((bothLeading_eval a c η hc (hd.2.trans he.2.symm) p q f _ _).symm.trans
      (evalRat_ofTwo (bothLeading a c η hc (hd.2.trans he.2.symm) p q f) v).symm))

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DegreeIdeals
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

lemma componentTensor_mul_components (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (k i j : T.Degrees) (x y : tensor (quotientFamily a μ) T) :
    componentTensor a μ T k (componentTensor a μ T i x * componentTensor a μ T j y)=
      if k=T.addDegrees i j then componentTensor a μ T i x * componentTensor a μ T j y else 0 := by
  induction T with
  | leaf d =>
    change componentB a μ d k (componentB a μ d i x * componentB a μ d j y)=_
    have hb:=componentB_mul_components a μ d k i j x y
    split_ifs with h
    · rw [ite_eq_left h] at hb
      exact hb
    · rw [ite_eq_right h] at hb
      exact hb
  | node l r hl hr =>
    have hp (xl yl : tensor (quotientFamily a μ) l) (xr yr : tensor (quotientFamily a μ) r) :
        componentTensor a μ (.node l r) k
          (componentTensor a μ (.node l r) i (xl ⊗ₜ[ℚ] xr) *
            componentTensor a μ (.node l r) j (yl ⊗ₜ[ℚ] yr))=
        if k=(.node l r : SplitTree I).addDegrees i j then
          componentTensor a μ (.node l r) i (xl ⊗ₜ[ℚ] xr) *
            componentTensor a μ (.node l r) j (yl ⊗ₜ[ℚ] yr) else 0 := by
      simp only [componentTensor,TensorProduct.map_tmul,Algebra.TensorProduct.tmul_mul_tmul,hl,hr]
      rcases k with ⟨kl,kr⟩
      by_cases hL : kl=l.addDegrees i.1 j.1 <;>
        by_cases hR : kr=r.addDegrees i.2 j.2 <;> simp [addDegrees,hL,hR]
    induction x using OAI.tensorInductionOn with
    | tmul xl xr =>
      induction y using OAI.tensorInductionOn with
      | tmul yl yr => simpa only using hp xl yl xr yr
      | add y z hy hz =>
        simp only [map_add,mul_add,hy,hz]
        split_ifs <;> simp
    | add x z hx hz =>
      simp only [map_add,add_mul,hx,hz]
      split_ifs <;> simp

lemma degreeCutSubmodule_mul_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x y : tensor (quotientFamily a μ) T)
    (hx : x∈degreeCutSubmodule a μ T W) : x*y∈degreeCutSubmodule a μ T W := by
  classical
  obtain ⟨s,hs,hxs⟩:=componentTensor_finite_decomposition a μ T x
  obtain ⟨t,ht,hyt⟩:=componentTensor_finite_decomposition a μ T y
  intro k hk
  conv_lhs => rw [←hxs,←hyt]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  rw [componentTensor_mul_components]
  split_ifs with heq
  · by_cases hj0 : T.NonnegativeDegree j
    · have hjnn:=T.totalDegree_nonnegative j hj0
      have hiw : 2*T.totalDegree i+T.doubleShift a<W := by
        rw [heq,T.totalDegree_addDegrees] at hk
        omega
      rw [hx i hiw,zero_mul]
    · simp only [componentTensor_negative a μ T j hj0,LinearMap.zero_apply,mul_zero]
  · rfl

noncomputable def degreeCutIdeal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) : Ideal (tensor (quotientFamily a μ) T) where
  __ := (degreeCutSubmodule a μ T W).toAddSubmonoid
  smul_mem' c x hx := by
    change c*x∈degreeCutSubmodule a μ T W
    rw [mul_comm]
    exact degreeCutSubmodule_mul_mem a μ T W x c hx

end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma degreeCut_mul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W V : ℤ) (x y : tensor (quotientFamily a μ) T)
    (hx : x∈degreeCutSubmodule a μ T W) (hy : y∈degreeCutSubmodule a μ T V) :
    x*y∈degreeCutSubmodule a μ T (W+V-T.doubleShift a) := by
  classical
  obtain ⟨s,hs,hxs⟩:=componentTensor_finite_decomposition a μ T x
  obtain ⟨t,ht,hyt⟩:=componentTensor_finite_decomposition a μ T y
  intro k hk
  conv_lhs => rw [←hxs,←hyt]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  rw [componentTensor_mul_components]
  split_ifs with heq
  · by_cases hiw : 2*T.totalDegree i+T.doubleShift a<W
    · rw [hx i hiw,zero_mul]
    · have hjv : 2*T.totalDegree j+T.doubleShift a<V := by
        rw [heq,T.totalDegree_addDegrees] at hk
        omega
      rw [hy j hjv,mul_zero]
  · rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Degree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SplitTree

lemma translationAtB_add (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (v w : T.Centers → ℚ) (x : tensor (quotientFamily a μ) T) :
    translationAtB a μ T v (translationAtB a μ T w x)=
      translationAtB a μ T (fun s=>v s+w s) x := by
  induction T with
  | leaf d => exact translationB_add a μ d (v ()) (w ()) x
  | node l r hl hr =>
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      change translationAtB a μ l (v ∘ Sum.inl) (translationAtB a μ l (w ∘ Sum.inl) x) ⊗ₜ[ℚ]
        translationAtB a μ r (v ∘ Sum.inr) (translationAtB a μ r (w ∘ Sum.inr) y)=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma restrictionB_translationAt (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (t : ℚ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    restrictionB a c η hc θ T hT (translationB a (SlopeArithmetic.slope c η) T.dim t f)=
      translationAtB a (SlopeArithmetic.slope c η) T (fun _=>t) (restrictionB a c η hc θ T hT f) := by
  induction T with
  | leaf d => rfl
  | node l r hl hr =>
    change (Algebra.TensorProduct.map (restrictionB a c η hc θ l hT.1)
      (restrictionB a c η hc θ r hT.2))
      (RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT.1).trans (slope_dim c η hc hT.2).symm) (firstCut l.dim r.dim)
        (translationB a (SlopeArithmetic.slope c η) (l.dim+r.dim) t f))=_
    rw [RawShuffle.restrictionB_translation]
    simp only [restrictionB,AlgHom.comp_apply]
    generalize RawShuffle.restrictionB a c η hc ((slope_dim c η hc hT.1).trans (slope_dim c η hc hT.2).symm) (firstCut l.dim r.dim) f=x
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      change restrictionB a c η hc θ l hT.1 (translationB a (SlopeArithmetic.slope c η) l.dim t x) ⊗ₜ[ℚ]
        restrictionB a c η hc θ r hT.2 (translationB a (SlopeArithmetic.slope c η) r.dim t y)=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma centeredRestrictionB_translate_eval (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (t : ℚ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) (v : T.Centers → ℚ) :
    evalRat v (centeredRestrictionB a c η hc θ T hT
      (translationB a (SlopeArithmetic.slope c η) T.dim t f))=
    evalRat (fun s=>v s+t) (centeredRestrictionB a c η hc θ T hT f) := by
  change evalRat v (centerTranslation _ _ T
    (restrictionB a c η hc θ T hT (translationB a (SlopeArithmetic.slope c η) T.dim t f)))=_
  rw [centerTranslation_evalRat,restrictionB_translationAt,translationAtB_add]
  exact (centerTranslation_evalRat _ _ _ _ _).symm
end SplitTree

lemma sourceFiltration_translation_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) (t : ℚ) :
    translationB a (SlopeArithmetic.slope c η) d t f∈sourceFiltration a c η hc θ d W := by
  intro T hT hs hd k z hw
  subst d
  let P:=SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k
  have h0 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs f)=0 := by
    ext s
    rw [coeff_mapLinear,MvPolynomial.coeff_zero]
    exact hf T hT hs rfl k s hw
  have h1 : mapLinear P (SplitTree.centeredRestrictionB a c η hc θ T hs
      (translationB a (SlopeArithmetic.slope c η) T.dim t f))=0 := by
    apply eq_of_evalRat
    intro v
    rw [map_zero,evalRat_mapLinear,SplitTree.centeredRestrictionB_translate_eval,
      ←evalRat_mapLinear,h0,map_zero]
  have he:=congrArg (fun polynomial => MvPolynomial.coeff z polynomial) h1
  change P ((SplitTree.centeredRestrictionB a c η hc θ T hs
    (translationB a (SlopeArithmetic.slope c η) T.dim t f)).coeff z)=0
  simpa only [coeff_mapLinear,MvPolynomial.coeff_zero,Finsupp.zero_apply] using he

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

lemma translationAtAlgB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (v : T.Centers → ℚ) (x : tensor (quotientFamily a μ) T) :
    translationAtAlgB a μ T v x=translationAtB a μ T v x := by
  induction T with
  | leaf d => exact translationAlgB_apply a μ d (v ()) x
  | node l r hl hr =>
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      change translationAtAlgB a μ l (v ∘ Sum.inl) x⊗ₜ[ℚ]
        translationAtAlgB a μ r (v ∘ Sum.inr) y=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossScalar
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CoefficientIdeals
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma sourceFiltration_mul_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (x y : B a (SlopeArithmetic.slope c η) d)
    (hx : x∈sourceFiltration a c η hc θ d W) :
    x*y∈sourceFiltration a c η hc θ d W := by
  intro T hT hs hd k z hw
  subst d
  let ρ:=SplitTree.centeredRestrictionB a c η hc θ T hs
  let J:=SplitTree.degreeCutIdeal a (SlopeArithmetic.slope c η) T W
  have hxc : ∀ m,(ρ x).coeff m∈J := by
    intro m j hj
    exact hx T hT hs rfl j m hj
  have hxy:=coeff_mul_mem J (ρ x) (ρ y) hxc z
  change SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k ((ρ (x*y)).coeff z)=0
  rw [map_mul]
  exact hxy k hw

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem sourceTensorFiltration_iff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :
    x∈sourceTensorFiltration a c η hc θ d e W ↔
      ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e,
        i.weight a+j.weight a<W → TensorProduct.map
          (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j) x=0 := by
  have hd : sourceFiltration a c η hc θ d =
      testFiltration (indexedRestriction a c η hc θ d) (RestrictionIndex.weight a) :=
    funext (sourceFiltration_eq_testFiltration a c η hc θ d)
  have he : sourceFiltration a c η hc θ e =
      testFiltration (indexedRestriction a c η hc θ e) (RestrictionIndex.weight a) :=
    funext (sourceFiltration_eq_testFiltration a c η hc θ e)
  unfold sourceTensorFiltration
  rw [hd,he]
  apply additiveTensorFiltration_iff_tests
    (L := -interaction a d d) (R := -interaction a e e)
  · rw [← hd,sourceFiltration_lower]
  · rw [← he,sourceFiltration_lower]

theorem tensor_leading_restrictions_detect (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)
    (hx : x∈sourceTensorFiltration a c η hc θ d e W)
    (h : ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e,
      i.weight a+j.weight a=W → TensorProduct.map
        (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j) x=0) :
    x∈sourceTensorFiltration a c η hc θ d e (W+1) := by
  rw [sourceTensorFiltration_iff] at hx ⊢
  intro i j hij
  by_cases heq : i.weight a+j.weight a=W
  · exact h i j heq
  · exact hx i j (by omega)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.IndependentCoefficientTensor
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma restrictionB_sourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    restrictionB a c η hc hs (firstCut d e) f∈sourceTensorFiltration a c η hc θ d e W := by
  rw [sourceTensorFiltration_iff]
  rintro ⟨T,hT,ht,hd,k,z⟩ ⟨U,hU,hu,he,l,w⟩ hw
  subst d
  subst e
  have hh:=sourceFiltration_allTrees a c η hc θ W f hf
    (.node T U) ⟨ht,hu⟩ rfl (k,l) (z.sumElim w)
  rw [SplitTree.restrictionTest_node (hT:=ht) (hU:=hu)] at hh
  apply hh
  change 2*(T.totalDegree k+U.totalDegree l)+(T.doubleShift a+U.doubleShift a)<W
  change (2*T.totalDegree k+T.doubleShift a)+(2*U.totalDegree l+U.doubleShift a)<W at hw
  omega

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SeparationCoefficients
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma sourceTensorFiltration_translateLeft (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) (t : ℚ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)
    (hx : x∈sourceTensorFiltration a c η hc θ d e W) :
    TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
      (LinearMap.id : B a (SlopeArithmetic.slope c η) e →ₗ[ℚ] B a (SlopeArithmetic.slope c η) e) x ∈
      sourceTensorFiltration a c η hc θ d e W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,f,g,hw,hf,hg,rfl⟩:=hx
    rw [TensorProduct.map_tmul,LinearMap.id_apply]
    exact tmul_mem_additiveTensorFiltration _ _ hw
      (sourceFiltration_translation_mem a c η hc θ d u f hf t) hg
  | zero => rw [map_zero]; exact (sourceTensorFiltration a c η hc θ d e W).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (sourceTensorFiltration a c η hc θ d e W).add_mem hx hy
  | smul q x _ hx =>
    rw [map_smul]
    exact (sourceTensorFiltration a c η hc θ d e W).smul_mem q hx

lemma restrictionRelativeB_coeff_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) (n : ℕ) :
    (restrictionRelativeB a c η hc hs (firstCut d e) f).coeff n∈
      sourceTensorFiltration a c η hc θ d e W := by
  apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
  intro t
  change (relativeTaylorB a (SlopeArithmetic.slope c η) d e
    (restrictionB a c η hc hs (firstCut d e) f)).eval _ ∈ _
  rw [relativeTaylorB_eval]
  exact sourceTensorFiltration_translateLeft a c η hc θ d e W t _
    (restrictionB_sourceTensorFiltration a c η hc θ d e hs W f hf)

noncomputable def sourceTensorFiltrationIdeal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    Ideal (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  additiveTensorFiltrationIdeal (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e)
    (sourceFiltration_mul_mem a c η hc θ d) (sourceFiltration_mul_mem a c η hc θ e) W

namespace SeparationInfinity

theorem separationCoefficient_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W j : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    separationCoefficient a c η hc hs j f∈sourceTensorFiltration a c η hc θ d e W := by
  rw [separationCoefficient_apply]
  apply ElementaryPositivity.LaurentAtInfinity.mulPolynomialCoeff_mem
    (sourceTensorFiltrationIdeal a c η hc θ d e W)
  exact restrictionRelativeB_coeff_filtration a c η hc θ d e hs W f hf
end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Restriction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.CoefficientIdeals
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sourceTensorFiltration_cross_cancel (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)
    (h : quotientTensor a (SlopeArithmetic.slope c η) d e (crossTensor d e)*x∈
      sourceTensorFiltration a c η hc θ d e W) :
    x∈sourceTensorFiltration a c η hc θ d e W := by
  let J:=sourceTensorFiltrationIdeal a c η hc θ d e W
  let q:=Ideal.Quotient.mk J
  have hh : ∀ n,(relativeTaylorB a (SlopeArithmetic.slope c η) d e
      (quotientTensor a (SlopeArithmetic.slope c η) d e (crossTensor d e)*x)).coeff n∈J := by
    apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
    intro t
    rw [relativeTaylorB_eval]
    exact sourceTensorFiltration_translateLeft a c η hc θ d e W t _ h
  have hz:= (polynomial_map_quotient_eq_zero_iff J _).mpr hh
  rw [map_mul,Polynomial.map_mul,←relativeTaylor_quotient] at hz
  change Polynomial.map q (crossClearing a (SlopeArithmetic.slope c η) d e)*
    Polynomial.map q (relativeTaylorB a (SlopeArithmetic.slope c η) d e x)=0 at hz
  have hx : Polynomial.map q (relativeTaylorB a (SlopeArithmetic.slope c η) d e x)=0 :=
    ((crossClearing_monic a (SlopeArithmetic.slope c η) d e).map q).mul_right_eq_zero_iff.mp hz
  have hc0:=(polynomial_map_quotient_eq_zero_iff J _).mp hx 0
  rwa [relativeTaylorB_coeff_zero] at hc0

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CenterLineSpecialization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refinedAtB_relative_eval (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (t : ℚ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim)) :
    refinedAtB a c η hc θ L R hL hR v w
      ((restrictionRelativeB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
        (firstCut L.dim R.dim) f).eval (algebraMap ℚ _ t))=
    evalRat (Sum.elim (fun z=>v z+t) w)
      (centeredRestrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f) := by
  change refinedAtB a c η hc θ L R hL hR v w
    ((relativeTaylorB a (SlopeArithmetic.slope c η) L.dim R.dim
      (RawShuffle.restrictionB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) (firstCut L.dim R.dim) f)).eval _) = _
  rw [relativeTaylorB_eval]
  trans translationAtB a (SlopeArithmetic.slope c η) (.node L R)
    (Sum.elim (fun z=>v z+t) w) (restrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f)
  · simp only [restrictionB,AlgHom.comp_apply]
    generalize RawShuffle.restrictionB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
      (firstCut L.dim R.dim) f=x
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      change translationAtAlgB a (SlopeArithmetic.slope c η) L v
        (restrictionB a c η hc θ L hL (translationB a (SlopeArithmetic.slope c η) L.dim t x)) ⊗ₜ[ℚ]
        translationAtAlgB a (SlopeArithmetic.slope c η) R w (restrictionB a c η hc θ R hR y)=_
      rw [translationAtAlgB_apply,translationAtAlgB_apply,restrictionB_translationAt,translationAtB_add]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  · exact (centerTranslation_evalRat a (SlopeArithmetic.slope c η) (.node L R)
      (restrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f) _).symm

lemma refinedAtB_relative_polynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim)) :
    (restrictionRelativeB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
      (firstCut L.dim R.dim) f).map (refinedAtB a c η hc θ L R hL hR v w).toRingHom=
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
      (centeredRestrictionB a c η hc θ (.node L R) ⟨hL,hR⟩ f) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,lineSpecialization_eval,refinedAtB_relative_eval]
  have he : Sum.elim (fun z=>v z+t) w =
      (fun i=>Sum.elim v w i+Sum.elim (fun _=>1) (fun _=>0) i*t) := by
    funext z
    cases z <;> simp
  rw [he]

lemma refinedAtB_relative_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) (n : ℕ) :
    ((restrictionRelativeB a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm)
      (firstCut L.dim R.dim) f).map (refinedAtB a c η hc θ L R hL hR v w).toRingHom).coeff n∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
  intro t
  rw [eval_map_rat,refinedAtB_relative_eval]
  exact centeredRestrictionB_eval_degreeCut a c η hc θ (.node L R) ⟨hL,hR⟩ W f hf _
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open HahnSeries
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma weightComponent_laurent_mul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ)
    (K F : LaurentSeries (tensor (quotientFamily a μ) T)) (q : LaurentSeries ℚ)
    (hF : ∀ k,F.coeff k∈degreeCutSubmodule a μ T W)
    (hK : mapRing (degreeZeroTensor a μ T).toRingHom K=
      mapRing (algebraMap ℚ (tensor (quotientFamily a μ) T)) q) :
    mapLinear (weightComponent a μ T W) (K*F)=
      mapRing (algebraMap ℚ (tensor (quotientFamily a μ) T)) q*
        mapLinear (weightComponent a μ T W) F := by
  let Q:=mapRing (algebraMap ℚ (tensor (quotientFamily a μ) T)) q
  have hpos : ∀ k,(K-Q).coeff k∈degreeCutSubmodule a μ T (T.doubleShift a+1) := by
    intro k
    have hh:=congrArg (fun x : LaurentSeries (tensor (quotientFamily a μ) T)=>x.coeff k) hK
    change degreeZeroTensor a μ T (K.coeff k)=Q.coeff k at hh
    rw [coeff_sub,←hh]
    exact sub_degreeZero_mem a μ T _
  have hz : mapLinear (weightComponent a μ T W) ((K-Q)*F)=0 := by
    apply HahnSeries.ext
    funext k
    change weightComponent a μ T W (((K-Q)*F).coeff k)=0
    apply degreeCut_weightComponent_zero
    have h:=coeff_mul_mem_of_pair
      (degreeCutSubmodule a μ T (T.doubleShift a+1)) (degreeCutSubmodule a μ T W)
      (degreeCutSubmodule a μ T (W+1))
      (fun x hx y hy=>by
        have hh:=degreeCut_mul a μ T (T.doubleShift a+1) W x y hx hy
        simpa only [show T.doubleShift a+1+W-T.doubleShift a=W+1 by omega] using hh)
      (K-Q) F hpos hF k
    exact h
  rw [sub_mul,map_sub] at hz
  rw [sub_eq_zero.mp hz,mapLinear_scalar_mul]
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RefinedLaurent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
open ElementaryPositivity.LaurentAtInfinity
open SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refined_relative_laurent_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) (k : ℤ) :
    (polynomial ((restrictionRelativeB a c η hc
      ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) (firstCut L.dim R.dim) f).map
        (refinedAtB a c η hc θ L R hL hR v w).toRingHom)).coeff k ∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  by_cases hk : 0<k
  · rw [polynomial_coeff_positive _ k hk]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).zero_mem
  · have he : k=-((-k).toNat : ℤ) := by omega
    rw [he,polynomial_coeff]
    exact refinedAtB_relative_coeff_degreeCut a c η hc θ L R hL hR v w W f hf _

lemma refined_leading_separation_formula (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    LaurentAtInfinity.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (separationSeries a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) f))=
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel a L R v w).val *
      polynomial (lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
        (totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f)) := by
  have hm := mapRing_mul_polynomial
    (refinedAtB a c η hc θ L R hL hR v w).toRingHom
    (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val
    (restrictionRelativeB a c η hc
      ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) (firstCut L.dim R.dim) f)
  change mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
    (separationSeries a c η hc ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) f)=_ at hm
  rw [hm]
  rw [weightComponent_laurent_mul a (SlopeArithmetic.slope c η) (.node L R) W _ _
    (scalarCrossKernel a L R v w).val
    (refined_relative_laurent_degreeCut a c η hc θ L R hL hR v w W f hf)
    (refined_inverseKernel_degreeZero a c η hc θ L R hL hR v w)]
  rw [refinedAtB_relative_polynomial,LaurentAtInfinity.polynomial_mapLinear,
    ←lineSpecialization_mapLinear]
  rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RefinedTensorDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refinedCenterPolynomial_eval (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : (L.node R).Centers → ℚ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    evalRat v (refinedCenterPolynomial a c η hc θ L R hL hR x)=
      refinedAtB a c η hc θ L R hL hR (v ∘ Sum.inl) (v ∘ Sum.inr) x := by
  have he : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr)=v := by funext z; cases z <;> rfl
  have ht:=centerTranslation_evalRat a (SlopeArithmetic.slope c η) (.node L R)
    (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL) (restrictionB a c η hc θ R hR) x) v
  change _=translationAtAlgB a (SlopeArithmetic.slope c η) (.node L R) _ _
  rw [translationAtAlgB_apply,he]
  exact ht

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitalSourceFiltration_mul_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (x y : B a (slope c η) d)
    (hx : x∈unitalSourceFiltration a c η hc θ d W) :
    x*y∈unitalSourceFiltration a c η hc θ d W := by
  classical
  by_cases hd : d=0
  · by_cases hw : W≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hw,Submodule.mem_top]
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hw,Submodule.mem_bot] at hx ⊢
      rw [hx,zero_mul]
  · rw [unitalSourceFiltration_nonzero a c η hc θ d hd W] at hx ⊢
    exact sourceFiltration_mul_mem a c η hc θ d W x y hx

lemma restrictionBUnit_unitalSourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (A : Cut d e) (W : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    restrictionBUnit a c η hc hs A f∈unitalSourceTensorFiltration a c η hc θ d e W := by
  by_cases hd : d=0
  · subst d
    have hr : restrictionBUnit a c η hc hs A f=(1 : B a (slope c η) 0)⊗ₜ[ℚ]castB a _ (zero_add e) f := by
      simpa only [castB_trans,castB_rfl] using restrictionBUnit_zero_left a c η hc A (castB a _ (zero_add e) f)
    rw [hr]
    exact tmul_mem_additiveTensorFiltration _ _ (by omega)
      (unitalSourceFiltration_unit a c η hc θ)
      (castB_mem_unitalSourceFiltration a c η hc θ (zero_add e) W hf)
  by_cases he : e=0
  · subst e
    have hr : restrictionBUnit a c η hc hs A f=castB a _ (add_zero d) f⊗ₜ[ℚ](1 : B a (slope c η) 0) := by
      simpa only [castB_trans,castB_rfl] using restrictionBUnit_zero_right a c η hc A (castB a _ (add_zero d) f)
    rw [hr]
    exact tmul_mem_additiveTensorFiltration _ _ (by omega)
      (castB_mem_unitalSourceFiltration a c η hc θ (add_zero d) W hf)
      (unitalSourceFiltration_unit a c η hc θ)
  have hde : d+e≠0 := add_ne_zero_left _ _ hd
  have hs' : slope c η d=slope c η e := hs.resolve_left hd |>.resolve_left he
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde W] at hf
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he W,
    restrictionBUnit_independent a c η hc hs A (firstCut d e),
    show restrictionBUnit a c η hc hs (firstCut d e)=restrictionB a c η hc hs' (firstCut d e) from rfl]
  exact restrictionB_sourceTensorFiltration a c η hc θ d e hs' W f hf

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourBraiding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM
lemma unitalSourceFiltration_translation_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (slope c η) d)
    (hf : f∈unitalSourceFiltration a c η hc θ d W) (t : ℚ) :
    translationB a (slope c η) d t f∈unitalSourceFiltration a c η hc θ d W := by
  classical
  by_cases hd : d=0
  · by_cases hw : W≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hw,Submodule.mem_top]
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hw,Submodule.mem_bot] at hf ⊢
      rw [hf,map_zero]
  · rw [unitalSourceFiltration_nonzero a c η hc θ d hd W] at hf ⊢
    exact sourceFiltration_translation_mem a c η hc θ d W f hf t

lemma unitalSourceTensorFiltration_translateLeft (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) (t : ℚ)
    (x : B a (slope c η) d ⊗[ℚ] B a (slope c η) e)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d e W) :
    TensorProduct.map (translationB a (slope c η) d t)
      (LinearMap.id : B a (slope c η) e →ₗ[ℚ] B a (slope c η) e) x ∈
      unitalSourceTensorFiltration a c η hc θ d e W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,f,g,hw,hf,hg,rfl⟩:=hx
    rw [TensorProduct.map_tmul,LinearMap.id_apply]
    exact tmul_mem_additiveTensorFiltration _ _ hw
      (unitalSourceFiltration_translation_mem a c η hc θ d u f hf t) hg
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [map_smul]; exact Submodule.smul_mem _ q hx

lemma unitalRestrictionRelativeB_coeff_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) (n : ℕ) :
    (unitalRestrictionRelativeB a c η hc hs f).coeff n∈unitalSourceTensorFiltration a c η hc θ d e W := by
  apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
  intro t
  change (relativeTaylorB a (slope c η) d e
    (restrictionBUnit a c η hc hs (firstCut d e) f)).eval _ ∈ _
  rw [relativeTaylorB_eval]
  exact unitalSourceTensorFiltration_translateLeft a c η hc θ d e W t _
    (restrictionBUnit_unitalSourceTensorFiltration a c η hc θ d e hs (firstCut d e) W f hf)

noncomputable def unitalSourceTensorFiltrationIdeal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) : Ideal (B a (slope c η) d⊗[ℚ]B a (slope c η) e) :=
  additiveTensorFiltrationIdeal (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e)
    (unitalSourceFiltration_mul_mem a c η hc θ d) (unitalSourceFiltration_mul_mem a c η hc θ e) W

namespace SeparationInfinity

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM
lemma unitalSeparationSeries_coeff_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W j : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    (unitalSeparationSeries a c η hc hs f).coeff j∈unitalSourceTensorFiltration a c η hc θ d e W := by
  have H := mulPolynomialCoeff_mem (unitalSourceTensorFiltrationIdeal a c η hc θ d e W)
    (quotientInverseKernelUnit a (slope c η) d e).val (-j)
    (unitalRestrictionRelativeB a c η hc hs f)
    (unitalRestrictionRelativeB_coeff_filtration a c η hc θ d e hs W f hf)
  change mulPolynomialCoeff (quotientInverseKernelUnit a (slope c η) d e).val (-j)
    (unitalRestrictionRelativeB a c η hc hs f)∈unitalSourceTensorFiltration a c η hc θ d e W at H
  simpa only [mulPolynomialCoeff_apply,neg_neg,unitalSeparationSeries,LinearMap.comp_apply,
    mulPolynomial_apply,AlgHom.toLinearMap_apply] using H

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearedSeparationB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.gridTensorBCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.gridTensorBAlgebra
lemma quotient_cellTransfer_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (ih₁ : ∀ u v x y,x∈unitalSourceFiltration a c η hc θ d₁ u →
      y∈unitalSourceFiltration a c η hc θ e₁ v →
      shuffleBUnit a c η hc d₁ e₁ h₁ x y∈unitalSourceFiltration a c η hc θ (d₁+e₁) (u+v))
    (ih₂ : ∀ u v x y,x∈unitalSourceFiltration a c η hc θ d₂ u →
      y∈unitalSourceFiltration a c η hc θ e₂ v →
      shuffleBUnit a c η hc d₂ e₂ h₂ x y∈unitalSourceFiltration a c η hc θ (d₂+e₂) (u+v))
    (U V : ℤ) (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (hf : quotientAlg a (slope c η) (d₁+d₂) f∈unitalSourceFiltration a c η hc θ (d₁+d₂) U)
    (hg : quotientAlg a (slope c η) (e₁+e₂) g∈unitalSourceFiltration a c η hc θ (e₁+e₂) V) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
      (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))∈
    unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) := by
  let F := unitalSourceFiltration a c η hc θ
  have hm (d) := unitalSourceFiltration_mul_mem a c η hc θ d
  have htf := restrictionBUnit_unitalSourceTensorFiltration a c η hc θ d₁ d₂ hd
    (firstCut d₁ d₂) U _ hf
  have htg := restrictionBUnit_unitalSourceTensorFiltration a c η hc θ e₁ e₂ he
    (firstCut e₁ e₂) V _ hg
  have hx := interchange_mem_filtration (F d₁) (F d₂) (F e₁) (F e₂) U V _ _ htf htg
  have hmul := additiveTensorFiltration_mul_mem
    (additiveTensorFiltration (F d₁) (F e₁)) (additiveTensorFiltration (F d₂) (F e₂))
    (additiveTensorFiltration_mul_mem (F d₁) (F e₁) (hm d₁) (hm e₁))
    (additiveTensorFiltration_mul_mem (F d₂) (F e₂) (hm d₂) (hm e₂)) (U+V) _
    (fourQuotient a (slope c η) d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)) hx
  erw [←fourQuotient_grid_factor a c η hc d₁ e₁ d₂ e₂ hd he
    (firstCut d₁ d₂) (firstCut e₁ e₂) f g] at hmul
  change quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
    (twoTargetTransfer a d₁ e₁ d₂ e₂ _)∈_
  rw [quotient_twoTargetTransfer_unit a c η hc d₁ e₁ d₂ e₂ h₁ h₂]
  exact tensor_map_mem_filtration _ _ (F (d₁+e₁)) (F (d₂+e₂))
    (shuffleTensorBUnit a c η hc d₁ e₁ h₁) (shuffleTensorBUnit a c η hc d₂ e₂ h₂)
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₁+e₁)) _ ih₁)
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₂+e₂)) _ ih₂)
    (U+V) _ hmul

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridShapeFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma quotient_fourGrid_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (ih₁ : ShuffleFiltered a c η hc θ d₁ e₁) (ih₂ : ShuffleFiltered a c η hc θ d₂ e₂)
    (h : d+e=(d₁+e₁)+(d₂+e₂)) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
      (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))∈
    unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) := by
  classical
  by_cases hd : d₁+d₂=d
  · have he : e₁+e₂=e := by
      apply add_left_cancel (a:=d)
      calc
        d+(e₁+e₂)=(d₁+e₁)+(d₂+e₂) := by rw [←hd]; ac_rfl
        _=d+e := h.symm
    subst d
    subst e
    exact quotient_cellTransfer_filtered a c η hc θ d₁ e₁ d₂ e₂
      (hon.1.compatible hon.2.2.1) (hon.2.1.compatible hon.2.2.2)
      (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)
      (ih₁ hon.1 hon.2.1) (ih₂ hon.2.2.1 hon.2.2.2) U V f g hf hg
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hd,map_zero,map_zero]
    exact Submodule.zero_mem _

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
omit [∀ i,Fintype (A i)] in
lemma quotient_gridShapeTensor_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e α β : I → ℕ} (h : d+e=α+β)
    (ihα : ∀ d' e',d'+e'=α → ShuffleFiltered a c η hc θ d' e')
    (ihβ : ∀ d' e',d'+e'=β → ShuffleFiltered a c η hc θ d' e')
    (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hon : CellsOnSlope c η θ
      (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)∈
      unitalSourceTensorFiltration a c η hc θ α β (U+V) := by
  have hα := (shape_add_complement u).trans (realization_card R)
  have hβ := (shape_add_complement v).trans (realization_card T)
  unfold gridShapeTensor
  apply quotientTensor_cast_mem_unitalSource
  apply quotient_fourGrid_filtered a c η hc θ _ _ _ _ hon
    (ihα _ _ hα) (ihβ _ _ hβ) _ U V f g hf hg
  rw [hα,hβ]
  exact h

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma restriction_shuffleBUnit_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e α β : I → ℕ) (hα : α≠0) (hβ : β≠0)
    (hdθ : slope c η d=θ) (hαθ : slope c η α=θ) (hβθ : slope c η β=θ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (h : α+β=d+e)
    (ihα : ∀ d' e',d'+e'=α → ShuffleFiltered a c η hc θ d' e')
    (ihβ : ∀ d' e',d'+e'=β → ShuffleFiltered a c η hc θ d' e')
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) e)
    (hf : f∈unitalSourceFiltration a c η hc θ d U)
    (hg : g∈unitalSourceFiltration a c η hc θ e V) :
    restrictionB a c η hc (hαθ.trans hβθ.symm) (firstCut α β)
      (castB a (slope c η) h.symm (shuffleBUnit a c η hc d e hs f g))∈
    sourceTensorFiltration a c η hc θ α β (U+V) := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      change restrictionB a c η hc (hαθ.trans hβθ.symm) (firstCut α β) (castB a (slope c η) h.symm
        (quotientAlg a (slope c η) (d+e) (shufflePolynomial a f g)))∈_
      rw [castB_mk,restrictionB_mk]
      apply sourceTensorFiltration_cross_cancel a c η hc θ α β (U+V)
      let R : Realization (α+β) (A:=fun i=>Fin ((α+β) i)) (fun _=>Finset.univ) :=
        fun _=>(Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm
      rw [cleared_restriction_sameSlope_support a c η hc h.symm f g R (firstCut α β)
        (hαθ.trans hβθ.symm) (hdθ.trans hαθ.symm)]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro x hx
      apply Submodule.sum_mem
      intro y hy
      split_ifs with hon
      · rw [←unitalSourceTensorFiltration_nonzero a c η hc θ α β hα hβ]
        apply quotient_gridShapeTensor_filtered a c η hc θ h.symm ihα ihβ U V f g hf hg
        rwa [hαθ] at hon
      · exact Submodule.zero_mem _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sourceFiltration_of_binary (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (slope c η) d)
    (hleaf : ∀ t : ℚ,translationB a (slope c η) d t f∈degreeCutSubmodule a (slope c η) (.leaf d) W)
    (hpair : ∀ (α β : I → ℕ) (_hα : α≠0) (_hβ : β≠0)
      (hsα : slope c η α=θ) (hsβ : slope c η β=θ) (h : α+β=d),
      RawShuffle.restrictionB a c η hc (hsα.trans hsβ.symm) (firstCut α β)
        (castB a (slope c η) h.symm f)∈sourceTensorFiltration a c η hc θ α β W) :
    f∈sourceFiltration a c η hc θ d W := by
  intro T hT hs hd k z hw
  subst d
  cases T with
  | leaf d =>
    have hz : z=Finsupp.single () (z ()) := by apply Finsupp.ext; intro u; cases u; simp
    rw [hz,restrictionTest_leaf_coeff]
    exact ElementaryPositivity.CommonTranslation.polynomial_coeff_mem (A:=B a (slope c η) d)
      (degreeCutSubmodule a (slope c η) (.leaf d) W) (taylorB a (slope c η) d f)
      (fun t => by erw [taylorB_eval]; exact hleaf t) (z ()) k hw
  | node T U =>
    cases T with
    | node T V => exact False.elim hT
    | leaf α =>
      let β:=U.dim
      have hr:=hpair α β hs.1.1 (dim_ne_zero hs.2) hs.1.2 (slope_dim c η hc hs.2) rfl
      have ht:=(sourceTensorFiltration_iff a c η hc θ α β W _).mp hr
      let z₁ := z.comapDomain Sum.inl Sum.inl_injective.injOn
      let z₂ := z.comapDomain Sum.inr Sum.inr_injective.injOn
      have hz : z₁.sumElim z₂=z := Finsupp.comapDomain_sumElim_comapDomain z
      rw [←hz,restrictionTest_node]
      exact ht ⟨.leaf α,trivial,hs.1,rfl,k.1,z₁⟩ ⟨U,hT,hs.2,rfl,k.2,z₂⟩ (by
        convert hw using 1; dsimp [RestrictionIndex.weight,totalDegree,doubleShift] <;> ring)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalGradeCoproduct (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ) :
    UnitalSourceGrade a c η hc θ (d+e) W →ₗ[ℚ] UnitalSourceTensorGrade a c η hc θ d e W :=
  LinearFiltration.map (unitalSourceFiltration a c η hc θ (d+e) W)
    (unitalSourceFiltration a c η hc θ (d+e) (W+1))
    (unitalSourceTensorFiltration a c η hc θ d e W)
    (unitalSourceTensorFiltration a c η hc θ d e (W+1))
    (unitalSeparationConstant a c η hc d e hs)
    (fun f hf=>unitalSeparationSeries_coeff_filtration a c η hc θ d e hs W 0 f hf)
    (fun f hf=>unitalSeparationSeries_coeff_filtration a c η hc θ d e hs (W+1) 0 f hf)

lemma unitalGradeCoproduct_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (W : ℤ)
    (f : unitalSourceFiltration a c η hc θ (d+e) W) :
    unitalGradeCoproduct a c η hc θ d e hs W (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk ⟨(unitalSeparationSeries a c η hc hs f.val).coeff 0,
        unitalSeparationSeries_coeff_filtration a c η hc θ d e hs W 0 f.val f.property⟩ :
        UnitalSourceTensorGrade a c η hc θ d e W) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open DimensionSplit SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def splitCoproductFiltration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ) :
    unitalSourceFiltration a c η hc θ d W →ₗ[ℚ]
      unitalSourceTensorFiltration a c η hc θ (left p) (right p) W :=
  (LinearFiltration.restrict _ _
    (unitalSeparationConstant a c η hc (left p) (right p) (hp.1.compatible hp.2))
    (fun x hx=>unitalSeparationSeries_coeff_filtration a c η hc θ _ _ (hp.1.compatible hp.2) W 0 x hx)).comp
    (unitalFiltrationCast a c η hc θ (left_add_right p).symm rfl).toLinearMap

noncomputable def splitCoproductGrade (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ) :
    UnitalSourceGrade a c η hc θ d W →ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ (left p) (right p) W :=
  (unitalGradeCoproduct a c η hc θ (left p) (right p) (hp.1.compatible hp.2) W).comp
    (unitalGradeCast a c η hc θ (left_add_right p).symm rfl).toLinearMap

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalShuffleCoproduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalSplitCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  (globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩
    ⟨right s.val,s.property.2⟩ k.2).comp
    ((unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2).comp
      (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl).toLinearMap)

noncomputable def globalHomogeneousCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  ∑ s : SlopeSplit c η hc θ k.1.val,globalSplitCoproduct a c η hc θ k s

noncomputable def globalCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) :
    UnitalShuffle a c η hc θ →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  DirectSum.toModule ℚ (SlopeWeight c η hc θ)
    (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)
    (globalHomogeneousCoproduct a c η hc θ)

lemma globalCoproduct_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    globalCoproduct a c η hc θ
      (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) k x)=
      ∑ s : SlopeSplit c η hc θ k.1.val,globalSplitCoproduct a c η hc θ k s x := by
  rw [globalCoproduct,DirectSum.toModule_lof]
  exact LinearMap.sum_apply _ _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end


