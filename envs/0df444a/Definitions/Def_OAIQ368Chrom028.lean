-- Prove2me | Definitions.Def_OAIQ368Chrom028
-- name    : OAIQ368Chrom028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:29:54.272565+00:00
-- url     : https://prove2.me/theorems/4847856a-0dca-4dbb-8230-ab9632b3bc2c
-- title:
--   Definitions bundle OAIQ368Chrom028 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 16 definitions, 1 instance and 40 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SplitTree.centerDenominator`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.crossPairs`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.crossPolynomial`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.degreeCutSubmodule`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.leadingPolynomial`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.pairRefinementCoefficient`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.refinedAtB`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.refinedCenterPolynomial`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.totalLeadingPolynomial`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.weightComponent`, `OAI.ElementaryPositivity.RawShuffle.clearedConstantB`, `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB`, `OAI.ElementaryPositivity.RawShuffle.commonRelativeLeading`, `OAI.ElementaryPositivity.RawShuffle.crossingColumnBAlg`, `OAI.ElementaryPositivity.RawShuffle.pairRelativeCoefficient`, `OAI.ElementaryPositivity.RawShuffle.relativeLeading`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Histories_TwoLeafDiagonal`, `Chromatic_Shuffle_AllPairDiagonal`, `Chromatic_Shuffle_BothTaylorB`, `Chromatic_Shuffle_ClearedSeparationB`, `Chromatic_Shuffle_CrossPolynomiality`, `Chromatic_Shuffle_Degree`, `Chromatic_Shuffle_DegreeIdeals`, `Chromatic_Shuffle_FourBraiding`, `Chromatic_Shuffle_Interaction`, `Chromatic_Shuffle_ManyBlockDiagonal`, `Chromatic_Shuffle_ManyBlockPolynomiality`, `Chromatic_Shuffle_PointEvaluation`, `Chromatic_Shuffle_Restriction`, `Chromatic_Shuffle_SymbolDetection`, `Chromatic_Shuffle_TaylorSCoeffHomogeneous`, `Chromatic_Shuffle_TensorDivisibility`, `Chromatic_Shuffle_TensorPolynomialBox`, `Chromatic_Shuffle_TwoTargetFiltration`, `Chromatic_Walls_CenterLineSpecialization`, `Chromatic_Walls_PolynomialCoeffLinear`, `Chromatic_Walls_RefinedLaurent`, `Chromatic_Walls_RefinedTensorDetection`, `Chromatic_Walls_TripleSymbols`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom031`, `OAIQ368Chrom032` and `OAIQ368Chrom037`; the statement `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head`; the proofs of `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` and `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom026

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TaylorSCoeffHomogeneous
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.Regroup.assocInv_centers_left _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.Regroup.assocInv_centers_mid _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centerTranslation_tmul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.componentFinsupp_apply _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.tensorValue_tmul _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma taylorS_coeff_homogeneous (d : I → ℕ) (f : S d) (k : ℤ)
    (hf : f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) (n : ℕ) :
    ((taylorS d f).coeff n).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) (k-n) := by
  have h := congrArg (fun p : Polynomial (MvPolynomial (Σi,Fin (d i)) ℚ)=>p.coeff n)
    (map_taylorSValue d f)
  rw [Polynomial.coeff_map] at h
  change ((taylorSValue d f).coeff n).val = (taylor f.val).coeff n at h
  change ((taylorSValue d f).coeff n).val.IsWeightedHomogeneous _ _
  rw [h]
  exact taylor_coeff_homogeneous f.val k hf n

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma componentTensor_componentTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (k l : T.Degrees) (f : tensor (quotientFamily a μ) T) :
    componentTensor a μ T k (componentTensor a μ T l f) =
      if k=l then componentTensor a μ T l f else 0 := by
  classical
  induction T with
  | leaf d =>
    split_ifs with h
    · subst l
      change componentB a μ d k (componentB a μ d k f) = componentB a μ d k f
      exact (componentB_componentB a μ d k k f).trans (ite_eq_left rfl)
    · change componentB a μ d k (componentB a μ d l f) = 0
      exact (componentB_componentB a μ d k l f).trans (ite_eq_right h)
  | node A B ihA ihB =>
    induction f using OAI.tensorInductionOn with
    | tmul x y =>
      by_cases hA : k.1=l.1 <;> by_cases hB : k.2=l.2 <;>
        simp [componentTensor,TensorProduct.map_tmul,ihA,ihB,Prod.ext_iff,hA,hB]
    | add x y hx hy =>
      simp only [map_add,hx,hy]
      split_ifs <;> simp

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma monomial_sumElim {α β : Type*} (x : α →₀ ℕ) (y : β →₀ ℕ) (c : ℚ) :
    monomial (x.sumElim y) c = rename Sum.inl (monomial x c) * rename Sum.inr (monomial y (1:ℚ)) := by
  rw [rename_monomial,rename_monomial,monomial_mul_monomial,mul_one,Finsupp.sumElim_eq_add]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialCoeffLinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
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

lemma coeff_single_toMvPolynomial {R α : Type*} [CommRing R] (i : α)
    (p : Polynomial R) (n : ℕ) :
    (Polynomial.toMvPolynomial i p).coeff (Finsupp.single i n)=p.coeff n := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,MvPolynomial.coeff_add,Finsupp.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial m r =>
    simp [← Polynomial.C_mul_X_pow_eq_monomial,MvPolynomial.coeff_X_pow,(Finsupp.single_injective i).eq_iff,eq_comm]

lemma restrictionTest_leaf_coeff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hs : (SplitTree.leaf d).OnSlope c η θ)
    (k : ℤ) (r : ℕ) (f : B a (SlopeArithmetic.slope c η) d) :
    restrictionTest a c η hc θ (.leaf d) hs rfl k (Finsupp.single () r) f =
      componentB a (SlopeArithmetic.slope c η) d k
        ((taylorB a (SlopeArithmetic.slope c η) d f).coeff r) := by
  change componentB a (SlopeArithmetic.slope c η) d k
    ((Polynomial.toMvPolynomial () (taylorB a (SlopeArithmetic.slope c η) d f)).coeff
      (Finsupp.single () r)) = _
  rw [coeff_single_toMvPolynomial]

noncomputable def relativeLeading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  (polynomialMapLinear (TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
    (componentB a (SlopeArithmetic.slope c η) e q))).comp
      ((relativeTaylorB a (SlopeArithmetic.slope c η) d e).toLinearMap.comp
        (restrictionB a c η hc hs (firstCut d e)).toLinearMap)

end ElementaryPositivity.RawShuffle

end

end OAI
end

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

lemma evalTwo_ext {A : Type*} [CommRing A] [Algebra ℚ A]
    (p q : Polynomial (Polynomial A)) (h : ∀ z w : ℚ,evalTwo p z w=evalTwo q z w) : p=q := by
  apply polynomial_eq_of_rat_evals
  intro w
  apply polynomial_eq_of_rat_evals
  intro z
  exact h z w

noncomputable def commonRelativeLeading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) : B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      Polynomial (Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)) :=
  (polynomialMapLinear (R:=B a (SlopeArithmetic.slope c η) (d+e))
    (S:=Polynomial (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e))
    (relativeLeading a c η hc (d:=d) (e:=e) hs p q)).comp
    (taylorB a (SlopeArithmetic.slope c η) (d+e)).toLinearMap

lemma commonRelativeLeading_eval (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (p q : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e)) (z w : ℚ) :
    evalTwo (commonRelativeLeading a c η hc hs p q f) z w =
      TensorProduct.map (componentB a (SlopeArithmetic.slope c η) d p)
        (componentB a (SlopeArithmetic.slope c η) e q)
        (TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d z)
          (LinearMap.id : B a (SlopeArithmetic.slope c η) e →ₗ[ℚ] B a (SlopeArithmetic.slope c η) e)
          (restrictionB a c η hc hs (firstCut d e)
            (translationB a (SlopeArithmetic.slope c η) (d+e) w f))) := by
  simp only [commonRelativeLeading,LinearMap.comp_apply,AlgHom.toLinearMap_apply,evalTwo,
    polynomialMapLinear_eval_rat,taylorB_eval]
  simp only [relativeLeading,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    polynomialMapLinear_eval_rat,relativeTaylorB_eval]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
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

noncomputable def pairRelativeCoefficient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (s : ℕ) (p q : ℤ) :
    B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e :=
  (polynomialCoeffLinear _ s).comp (relativeLeading a c η hc hs p q)

namespace SplitTree

noncomputable def pairRefinementCoefficient (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) {d e : I → ℕ}
    (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (T : SplitTree I) (s : ℕ) (p q : ℤ) (k : T.Degrees) :
    tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node (.leaf (d+e)) T) →ₗ[ℚ]
      tensor (quotientFamily a (SlopeArithmetic.slope c η))
        (.node (.node (.leaf d) (.leaf e)) T) :=
  TensorProduct.map (pairRelativeCoefficient a c η hc hs s p q)
    (componentTensor a (SlopeArithmetic.slope c η) T k)

end SplitTree
end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma evalRat_mapAlgHom {A D α : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (f : A →ₐ[ℚ] D)
    (p : MvPolynomial α A) (v : α → ℚ) :
    evalRat v (map f.toRingHom p) = f (evalRat v p) := by
  have he : map f.toRingHom p = mapLinear f.toLinearMap p := by ext s; simp only [coeff_map,coeff_mapLinear,AlgHom.toLinearMap_apply]; rfl
  rw [he,evalRat_mapLinear]
  rfl

lemma toRelative_mapLinear {A D α : Type*} [CommRing A] [CommRing D]
    [Algebra ℚ A] [Algebra ℚ D] (l : A →ₗ[ℚ] D)
    (p : MvPolynomial ((Unit ⊕ Unit) ⊕ α) A) :
    toRelative (mapLinear l p) = mapLinear (polynomialMapLinear l) (toRelative p) := by
  apply eq_of_evalRat
  intro v
  apply polynomial_eq_of_rat_evals
  intro t
  rw [evalRat_toRelative,evalRat_mapLinear,evalRat_mapLinear,
    polynomialMapLinear_eval_rat,evalRat_toRelative]

lemma restrictionB_two (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    restrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ f =
      RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e) f := by
  let μ := SlopeArithmetic.slope c η
  change (Algebra.TensorProduct.map (AlgHom.id ℚ (B a μ d)) (AlgHom.id ℚ (B a μ e)))
    (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e) f) = _
  rw [Algebra.TensorProduct.map_id]
  rfl

lemma restrictionB_pairRefinement (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i, 0 < c i) (θ : ℝ) {d e : I → ℕ}
    (hd : (.leaf d : SplitTree I).OnSlope c η θ)
    (he : (.leaf e : SplitTree I).OnSlope c η θ)
    (T : SplitTree I) (hT : T.OnSlope c η θ)
    (f : B a (SlopeArithmetic.slope c η) ((d+e)+T.dim)) :
    restrictionB a c η hc θ (.node (.node (.leaf d) (.leaf e)) T) ⟨⟨hd,he⟩,hT⟩ f =
      TensorProduct.map
        (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e)).toLinearMap
        (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
          tensor (quotientFamily a (SlopeArithmetic.slope c η)) T)
        (restrictionB a c η hc θ (.node (.leaf (d+e)) T)
          ⟨⟨SlopeArithmetic.add_ne_zero_left d e hd.1,
            (SlopeArithmetic.slope_add_same c η hc (hd.2.trans he.2.symm)).trans hd.2⟩,hT⟩ f) := by
  let hs := (SlopeArithmetic.slope_add_same c η hc (hd.2.trans he.2.symm)).trans
    (hd.2.trans (slope_dim c η hc hT).symm)
  let y := RawShuffle.restrictionB a c η hc hs (firstCut (d+e) T.dim) f
  change Algebra.TensorProduct.map
      (restrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩)
      (restrictionB a c η hc θ T hT) y =
    TensorProduct.map
      (RawShuffle.restrictionB a c η hc (hd.2.trans he.2.symm) (firstCut d e)).toLinearMap
      (LinearMap.id : tensor (quotientFamily a (SlopeArithmetic.slope c η)) T →ₗ[ℚ]
        tensor (quotientFamily a (SlopeArithmetic.slope c η)) T)
      (Algebra.TensorProduct.map (AlgHom.id ℚ _)
        (restrictionB a c η hc θ T hT) y)
  generalize y = x
  induction x using OAI.tensorInductionOn with
  | tmul g h =>
    change restrictionB a c η hc θ (.node (.leaf d) (.leaf e)) ⟨hd,he⟩ g ⊗ₜ[ℚ]
      restrictionB a c η hc θ T hT h = _
    rw [restrictionB_two a c η hc θ hd he]
    rfl
  | add x y hx hy => simp only [map_add,hx,hy]; rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TwoLeafDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
universe u
variable {I : Type u}

namespace Regroup

lemma leafDimension {T U : SplitTree I} (e : Regroup T U) (i : T.Centers) :
    U.leafDimension (e.centers i) = T.leafDimension i := by
  induction e with
  | refl T => rfl
  | assoc T U V => rcases i with (i|i)|i <;> rfl
  | swap T U => cases i <;> rfl
  | node e f ihe ihf => cases i with
    | inl i => exact ihe i
    | inr i => exact ihf i
  | trans e f ihe ihf => exact (ihf (e.centers i)).trans (ihe i)

lemma isolate_one (T : SplitTree I) (i : T.Centers) :
    (∃ d, ∃ e : Regroup T (.leaf d), e.centers i = ()) ∨
    (∃ d U, ∃ e : Regroup T (.node (.leaf d) U), e.centers i = Sum.inl ()) := by
  induction T with
  | leaf d =>
    left
    exact ⟨d,.refl _,Subsingleton.elim _ _⟩
  | node l r ihl ihr =>
    cases i with
    | inl i =>
      rcases ihl i with ⟨d,e,he⟩ | ⟨d,U,e,he⟩
      · right
        refine ⟨d,r,.node e (.refl r),?_⟩
        exact congrArg Sum.inl he
      · right
        refine ⟨d,.node U r,(Regroup.node e (.refl r)).trans (Regroup.assoc _ _ _),?_⟩
        change (Equiv.sumAssoc _ _ _) (Sum.inl (e.centers i)) = _
        rw [he]
        rfl
    | inr i =>
      rcases ihr i with ⟨d,e,he⟩ | ⟨d,U,e,he⟩
      · right
        refine ⟨d,l,(Regroup.swap l r).trans (.node e (.refl l)),?_⟩
        exact congrArg Sum.inl he
      · right
        refine ⟨d,.node U l,(Regroup.swap l r).trans
          ((Regroup.node e (.refl l)).trans (Regroup.assoc _ _ _)),?_⟩
        change (Equiv.sumAssoc _ _ _) (Sum.inl (e.centers i)) = _
        rw [he]
        rfl

lemma isolate_pair (T : SplitTree I) (i j : T.Centers) (hij : i ≠ j) :
    (∃ d e, ∃ g : Regroup T (.node (.leaf d) (.leaf e)),
      g.centers i = Sum.inl () ∧ g.centers j = Sum.inr ()) ∨
    (∃ d e U, ∃ g : Regroup T (.node (.node (.leaf d) (.leaf e)) U),
      g.centers i = Sum.inl (Sum.inl ()) ∧ g.centers j = Sum.inl (Sum.inr ())) := by
  rcases isolate_one T i with ⟨d,g,hg⟩ | ⟨d,R,g,hg⟩
  · exact (hij (g.centers.injective (Subsingleton.elim _ _))).elim
  · cases hj : g.centers j with
    | inl t =>
      cases t
      exact (hij (g.centers.injective (hg.trans hj.symm))).elim
    | inr k =>
      rcases isolate_one R k with ⟨e,h,hh⟩ | ⟨e,U,h,hh⟩
      · left
        refine ⟨d,e,g.trans (.node (.refl _) h),?_,?_⟩
        · change (Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers i) = _
          rw [hg]
          rfl
        · change (Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers j) = _
          rw [hj]
          exact congrArg Sum.inr hh
      · right
        refine ⟨d,e,U,g.trans ((Regroup.node (.refl _) h).trans (assocInv _ _ _)),?_,?_⟩
        · change (assocInv _ _ _).centers
            ((Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers i)) = _
          rw [hg]
          rfl
        · change (assocInv _ _ _).centers
            ((Equiv.sumCongr (Equiv.refl _) h.centers) (g.centers j)) = _
          rw [hj]
          change (assocInv _ _ _).centers (Sum.inr (h.centers k)) = _
          rw [hh]
          rfl

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_AllPairDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

noncomputable def leadingPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (k : T.Degrees) (f : B a (SlopeArithmetic.slope c η) T.dim) :=
  mapLinear (componentTensor a (SlopeArithmetic.slope c η) T k)
    (centeredRestrictionB a c η hc θ T hT f)

lemma Regroup.leadingPolynomial_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ) (k : T.Degrees)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    leadingPolynomial a c η hc θ U hU (e.degrees k)
      (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f) =
    extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
      e.centers (leadingPolynomial a c η hc θ T hT k f) := by
  unfold leadingPolynomial
  rw [e.centeredRestrictionB_natural a c η hc θ hT hU]
  apply mapLinear_extendPolynomial
  intro x
  exact (e.componentTensor_natural a (SlopeArithmetic.slope c η) k x).symm

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockPolynomiality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def centerDenominator (a : I → I → ℕ) (T : SplitTree I)
    (s : Finset (T.Centers × T.Centers)) : MvPolynomial T.Centers ℚ :=
  ∏ ij ∈ s, diagonal ij.1 ij.2 ^
    (-eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2)).toNat

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def weightComponent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) :
    tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T := by
  classical
  exact (Finsupp.lsum ℚ (fun k : T.Degrees=>
    if 2*T.totalDegree k+T.doubleShift a=W then LinearMap.id else 0)).comp
    (componentFinsupp a μ T)

lemma weightComponent_eq_sum (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x : tensor (quotientFamily a μ) T) (s : Finset T.Degrees)
    (hs : ∀ k∉s, componentTensor a μ T k x=0) :
    weightComponent a μ T W x = ∑ k∈s,
      if 2*T.totalDegree k+T.doubleShift a=W then componentTensor a μ T k x else 0 := by
  classical
  unfold weightComponent
  rw [LinearMap.comp_apply,Finsupp.lsum_apply]
  have hsub : (componentFinsupp a μ T x).support ⊆ s := by
    intro k hk
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hk) (hs k hn)
  rw [Finsupp.sum_of_support_subset _ hsub _ (by intro k hk; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> rfl

lemma componentTensor_weightComponent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x : tensor (quotientFamily a μ) T) (k : T.Degrees) :
    componentTensor a μ T k (weightComponent a μ T W x) =
      if 2*T.totalDegree k+T.doubleShift a=W then componentTensor a μ T k x else 0 := by
  classical
  obtain ⟨s,hs,he⟩ := componentTensor_finite_decomposition a μ T x
  rw [weightComponent_eq_sum a μ T W x s hs,map_sum]
  simp only [apply_ite,componentTensor_componentTensor,map_zero]
  by_cases hk : k∈s
  · rw [Finset.sum_eq_single k]
    · by_cases hw : 2*T.totalDegree k+T.doubleShift a=W <;> simp [hw]
    · intro j hj hne
      simp [Ne.symm hne]
    · exact fun h=>False.elim (h hk)
  · rw [hs k hk]
    simp only [ite_self]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : k≠j := fun h=>hk (h ▸ hj)
    simp [hne]

lemma polynomial_component_finite (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (p : MvPolynomial T.Centers (tensor (quotientFamily a μ) T)) :
    ∃ s : Finset T.Degrees, ∀ k∉s, mapLinear (componentTensor a μ T k) p=0 := by
  classical
  let s := p.support.biUnion (fun z=>(componentFinsupp a μ T (p.coeff z)).support)
  refine ⟨s,?_⟩
  intro k hk
  ext z
  simp only [coeff_mapLinear,MvPolynomial.coeff_zero,Finsupp.zero_apply]
  by_cases hz : z∈p.support
  · have hnot : k∉(componentFinsupp a μ T (p.coeff z)).support := fun h=>
      hk (Finset.mem_biUnion.mpr ⟨z,hz,h⟩)
    exact Finsupp.notMem_support_iff.mp hnot
  · rw [notMem_support_iff.mp hz,map_zero]

lemma mapLinear_weightComponent_eq_sum (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (p : MvPolynomial T.Centers (tensor (quotientFamily a μ) T))
    (s : Finset T.Degrees) (hs : ∀ k∉s, mapLinear (componentTensor a μ T k) p=0) :
    mapLinear (weightComponent a μ T W) p = ∑ k∈s,
      if 2*T.totalDegree k+T.doubleShift a=W then mapLinear (componentTensor a μ T k) p else 0 := by
  classical
  ext z
  simp only [coeff_mapLinear,coeff_sum,apply_ite,MvPolynomial.coeff_zero,
    DFunLike.ite_apply,Finsupp.zero_apply]
  apply weightComponent_eq_sum
  intro k hk
  have h := congrArg (fun polynomial => MvPolynomial.coeff z polynomial) (hs k hk)
  simpa only [coeff_mapLinear,MvPolynomial.coeff_zero,Finsupp.zero_apply] using h

noncomputable def totalLeadingPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim) :=
  mapLinear (weightComponent a (SlopeArithmetic.slope c η) T W)
    (centeredRestrictionB a c η hc θ T hT f)

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DegreeIdeals
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
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

omit [Fintype I] [DecidableEq I] in
lemma totalDegree_addDegrees (T : SplitTree I) (i j : T.Degrees) :
    T.totalDegree (T.addDegrees i j)=T.totalDegree i+T.totalDegree j := by
  induction T with
  | leaf d => rfl
  | node l r hl hr =>
    simp only [totalDegree,hl,hr]
    omega

noncomputable def degreeCutSubmodule (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) : Submodule ℚ (tensor (quotientFamily a μ) T) where
  carrier := {x | ∀ k,2*T.totalDegree k+T.doubleShift a<W → componentTensor a μ T k x=0}
  zero_mem' := by intro k hk; exact (componentTensor a μ T k).map_zero
  add_mem' := by intro x y hx hy k hk; simp only [map_add,hx k hk,hy k hk,add_zero]
  smul_mem' := by intro c x hx k hk; simp only [map_smul,hx k hk,smul_zero]

end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma degreeCut_weightComponent_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x : tensor (quotientFamily a μ) T)
    (hx : x∈degreeCutSubmodule a μ T (W+1)) : weightComponent a μ T W x=0 := by
  classical
  obtain ⟨s,hs,hxs⟩:=componentTensor_finite_decomposition a μ T x
  rw [weightComponent_eq_sum a μ T W x s hs]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hw
  · exact hx i (by omega)
  · rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Degree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
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

omit [Fintype I] [DecidableEq I] in
lemma nonnegativeDegree_zeroDegrees (T : SplitTree I) : T.NonnegativeDegree T.zeroDegrees := by
  induction T with
  | leaf d => exact le_rfl
  | node l r hl hr => exact ⟨hl,hr⟩

omit [Fintype I] [DecidableEq I] in
lemma nonnegative_totalDegree_zero (T : SplitTree I) (k : T.Degrees)
    (hn : T.NonnegativeDegree k) (hk : T.totalDegree k=0) : k=T.zeroDegrees := by
  induction T with
  | leaf d => exact hk
  | node l r hl hr =>
    have hL:=l.totalDegree_nonnegative k.1 hn.1
    have hR:=r.totalDegree_nonnegative k.2 hn.2
    change l.totalDegree k.1+r.totalDegree k.2=0 at hk
    exact Prod.ext (hl k.1 hn.1 (by omega)) (hr k.2 hn.2 (by omega))

lemma degreeZeroTensor_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) :
    degreeZeroTensor a μ T x=componentTensor a μ T T.zeroDegrees x := by
  induction T with
  | leaf d => rfl
  | node l r hl hr =>
    induction x using OAI.tensorInductionOn with
    | tmul x y =>
      change degreeZeroTensor a μ l x⊗ₜ[ℚ]degreeZeroTensor a μ r y=_
      rw [hl,hr]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

lemma sub_degreeZero_mem (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) :
    x-degreeZeroTensor a μ T x∈degreeCutSubmodule a μ T (T.doubleShift a+1) := by
  intro k hk
  rw [degreeZeroTensor_apply,map_sub,componentTensor_componentTensor]
  by_cases hn : T.NonnegativeDegree k
  · have hnn:=T.totalDegree_nonnegative k hn
    have hz : k=T.zeroDegrees := nonnegative_totalDegree_zero T k hn (by omega)
    simp only [hz,ite_true, if_true,sub_self]
  · have hne : k≠T.zeroDegrees := by
      intro h
      apply hn
      simpa only [h] using T.nonnegativeDegree_zeroDegrees
    simp only [ite_eq_right hne,componentTensor_negative a μ T k hn,LinearMap.zero_apply,sub_zero]
end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

instance centersLinearOrder : (T : SplitTree I) → LinearOrder T.Centers
  | .leaf _ => inferInstanceAs (LinearOrder Unit)
  | .node l r => by
    letI := centersLinearOrder l
    letI := centersLinearOrder r
    exact Sum.Lex.linearOrder

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Restriction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma relativeTaylorB_coeff_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d ⊗[ℚ] B a μ e) : (relativeTaylorB a μ d e x).coeff 0=x := by
  rw [Polynomial.coeff_zero_eq_eval_zero,←map_zero (algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e)),relativeTaylorB_eval]
  have he : translationB a μ d 0=LinearMap.id := LinearMap.ext (translationB_zero a μ d)
  rw [he,TensorProduct.map_id,LinearMap.id_apply]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree
omit [DecidableEq I] in
lemma leafDimension_onSlope (T : SplitTree I) (c η : I → ℝ) (θ : ℝ)
    (hT : T.OnSlope c η θ) (i : T.Centers) :
    T.leafDimension i≠0 ∧ SlopeArithmetic.slope c η (T.leafDimension i)=θ := by
  induction T with
  | leaf d => exact hT
  | node l r hl hr =>
    cases i with
    | inl i => exact hl hT.1 i
    | inr i => exact hr hT.2 i

end SplitTree

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CenterLineSpecialization
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

noncomputable def refinedAtB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim →ₐ[ℚ]
      tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R) :=
  (translationAtAlgB a (SlopeArithmetic.slope c η) (.node L R) (Sum.elim v w)).comp
    (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL) (restrictionB a c η hc θ R hR))

lemma degreeZero_refinedAtB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)
      (refinedAtB a c η hc θ L R hL hR v w x)=
      pointedTensorRestriction a c η hc θ L R hL hR v w x := by
  induction x using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma centeredRestrictionB_eval_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W) (v : T.Centers → ℚ) :
    evalRat v (centeredRestrictionB a c η hc θ T hT f)∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) T W := by
  intro k hk
  have hz : mapLinear (componentTensor a (SlopeArithmetic.slope c η) T k)
      (centeredRestrictionB a c η hc θ T hT f)=0 := by
    ext m
    rw [coeff_mapLinear,MvPolynomial.coeff_zero]
    exact sourceFiltration_allTrees a c η hc θ W f hf T hT rfl k m hk
  rw [←evalRat_mapLinear,hz,map_zero]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorPolynomialBox
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma centeredRestrictionB_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W) (z : T.Centers →₀ ℕ) :
    (centeredRestrictionB a c η hc θ T hT f).coeff z∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) T W := by
  intro k hk
  exact sourceFiltration_allTrees a c η hc θ W f hf T hT rfl k z hk

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossPolynomiality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def crossPairs (L R : SplitTree I) : Finset ((L.node R).Centers×(L.node R).Centers) :=
  Finset.univ.image (fun p : L.Centers×R.Centers=>(Sum.inl p.1,Sum.inr p.2))

omit [Fintype I] [DecidableEq I] in
lemma crossPairs_injective (L R : SplitTree I) :
    Function.Injective (fun p : L.Centers×R.Centers=>((Sum.inl p.1,Sum.inr p.2) : (L.node R).Centers×(L.node R).Centers)) := by
  intro p q h
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h)) (Sum.inr.inj (congrArg Prod.snd h))

omit [Fintype I] [DecidableEq I] in
lemma crossPairs_ne (L R : SplitTree I) (p : (L.node R).Centers×(L.node R).Centers)
    (hp : p∈crossPairs L R) : p.1≠p.2 := by
  obtain ⟨⟨x,y⟩,_,rfl⟩:=Finset.mem_image.mp hp
  exact Sum.inl_ne_inr

omit [Fintype I] [DecidableEq I] in
lemma crossPairs_norev (L R : SplitTree I) (p : (L.node R).Centers×(L.node R).Centers)
    (hp : p∈crossPairs L R) : (p.2,p.1)∉crossPairs L R := by
  obtain ⟨⟨x,y⟩,_,rfl⟩:=Finset.mem_image.mp hp
  intro h
  obtain ⟨⟨z,t⟩,_,h⟩:=Finset.mem_image.mp h
  exact Sum.inl_ne_inr (congrArg Prod.fst h)

omit [DecidableEq I] in
lemma crossPairs_symmetric (a : I → I → ℕ) (c η : I → ℝ) (θ : ℝ)
    (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (p : (L.node R).Centers×(L.node R).Centers) (hp : p∈crossPairs L R) :
    eulerForm a ((L.node R).leafDimension p.1) ((L.node R).leafDimension p.2)=
      eulerForm a ((L.node R).leafDimension p.2) ((L.node R).leafDimension p.1) := by
  obtain ⟨⟨x,y⟩,_,rfl⟩:=Finset.mem_image.mp hp
  obtain ⟨hx,hsx⟩:=L.leafDimension_onSlope c η θ hL x
  obtain ⟨hy,hsy⟩:=R.leafDimension_onSlope c η θ hR y
  exact hχ _ _ hx hy hsx hsy

noncomputable def crossPolynomial (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (e : ℤ → ℕ) : Polynomial ℚ :=
  ∏ z : L.Centers,∏ t : R.Centers,
    affinePolynomial (w t-v z) ^ e (eulerForm a (L.leafDimension z) (R.leafDimension t))

omit [DecidableEq I] in
lemma centerDenominator_crossPairs_line (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
      (centerDenominator a (L.node R) (crossPairs L R))=
      crossPolynomial a L R v w (fun e=>(-e).toNat) := by
  classical
  unfold centerDenominator crossPairs
  rw [Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h)]
  simp only [map_prod,map_pow]
  rw [Fintype.prod_prod_type]
  unfold crossPolynomial
  apply Finset.prod_congr rfl
  intro z hz
  apply Finset.prod_congr rfl
  intro t ht
  congr 1
  simp only [diagonal,map_sub,lineSpecialization_X,Sum.elim_inl,Sum.elim_inr,
    _root_.map_zero,_root_.map_one,zero_mul,one_mul,add_zero,Algebra.algebraMap_self_apply,
    affinePolynomial]
  ring

omit [DecidableEq I] in
lemma scalarCrossKernel_denominator (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    (scalarCrossKernel a L R v w : LaurentSeries ℚ)*
      polynomial (crossPolynomial a L R v w (fun e=>(-e).toNat))=
      polynomial (crossPolynomial a L R v w Int.toNat) := by
  unfold scalarCrossKernel crossPolynomial
  simp only [map_prod,Units.coe_prod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro z hz
  rw [←Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht=>affineUnit_zpow_cancel _ _

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RefinedLaurent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma refined_inverseKernel_degreeZero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val)=
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel a L R v w).val := by
  trans mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
    (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val
  · apply HahnSeries.ext
    funext k
    exact degreeZero_refinedAtB a c η hc θ L R hL hR v w _
  · rw [pointed_quotientInverseKernel]
    congr 1
    exact congrArg Units.val (crossPointEval_inverseKernel_scalar a L R v w)

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

noncomputable def refinedCenterPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  centerTranslation (quotientFamily a (SlopeArithmetic.slope c η)) (taylorB a (SlopeArithmetic.slope c η))
    (.node L R) (Algebra.TensorProduct.map (restrictionB a c η hc θ L hL)
      (restrictionB a c η hc θ R hR) x)

lemma refinedCenterPolynomial_coeff_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (k : L.Degrees) (l : R.Degrees) (z : L.Centers →₀ ℕ) (w : R.Centers →₀ ℕ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim) :
    componentTensor a (SlopeArithmetic.slope c η) (.node L R) (k,l)
      ((refinedCenterPolynomial a c η hc θ L R hL hR x).coeff (z.sumElim w))=
      TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
        (restrictionTest a c η hc θ R hR rfl l w) x := by
  unfold refinedCenterPolynomial
  rw [centerTranslation_node_coeff]
  induction x using OAI.tensorInductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorDivisibility
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refinedCenterPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (x : B a (SlopeArithmetic.slope c η) L.dim)
    (y : B a (SlopeArithmetic.slope c η) R.dim) :
    refinedCenterPolynomial a c η hc θ L R hL hR (x⊗ₜ[ℚ]y)=
      box (centeredRestrictionB a c η hc θ L hL x)
        (centeredRestrictionB a c η hc θ R hR y) := by
  unfold refinedCenterPolynomial
  rw [Algebra.TensorProduct.map_tmul]
  erw [centerTranslation_tmul]
  rfl

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TripleSymbols
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma refinedCenterPolynomial_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim W) (z : (L.node R).Centers →₀ ℕ) :
    (refinedCenterPolynomial a c η hc θ L R hL hR x).coeff z∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U,V,x,y,hUV,hx,hy,rfl⟩:=hx
    rw [refinedCenterPolynomial_tmul,←Finsupp.comapDomain_sumElim_comapDomain z,coeff_box]
    rintro ⟨k,l⟩ hkl
    change componentTensor a (SlopeArithmetic.slope c η) L k _⊗ₜ[ℚ]
      componentTensor a (SlopeArithmetic.slope c η) R l _=0
    change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)<W at hkl
    by_cases hk : 2*L.totalDegree k+L.doubleShift a<U
    · rw [centeredRestrictionB_coeff_degreeCut a c η hc θ L hL U x hx _ k hk,
        TensorProduct.zero_tmul]
    · rw [centeredRestrictionB_coeff_degreeCut a c η hc θ R hR V y hy _ l (by omega),
        TensorProduct.tmul_zero]
  | zero =>
    simp only [refinedCenterPolynomial,map_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply]
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).zero_mem
  | add x y hx hy ihx ihy =>
    simp only [refinedCenterPolynomial,map_add,MvPolynomial.coeff_add,Finsupp.add_apply] at ihx ihy ⊢
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).add_mem ihx ihy
  | smul r x hx ih =>
    simp only [refinedCenterPolynomial,map_smul,coeff_smul] at ih ⊢
    exact (degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W).smul_mem r ih

end ElementaryPositivity.RawShuffle.SplitTree

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
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorM
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourM
noncomputable def crossingColumnBAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    B a μ e₁⊗[ℚ]B a μ d₂ →ₐ[ℚ](B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  middleEmbedding

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearedSeparationB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance clearBTensorS_reea90d_1 (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearBTensorSA_reea90d_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorB
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorBA
noncomputable def clearedSeparationB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d⊗[ℚ]B a μ e →ₗ[ℚ] LaurentSeries (B a μ d⊗[ℚ]B a μ e) :=
  (mulPolynomial (mixedInverseKernelUnit a a μ d e *
    (mixedInverseKernelUnit a (fun _ _ : I=>0) μ d e)⁻¹).val).comp
      (relativeTaylorB a μ d e).toLinearMap

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TwoTargetFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

noncomputable def clearedConstantB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d⊗[ℚ]B a μ e →ₗ[ℚ] B a μ d⊗[ℚ]B a μ e :=
  (coeff.linearMap (R:=ℚ) 0).comp (clearedSeparationB a μ d e)

end ElementaryPositivity.RawShuffle

end

end OAI
end


