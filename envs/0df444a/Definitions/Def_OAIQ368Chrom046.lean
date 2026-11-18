-- Prove2me | Definitions.Def_OAIQ368Chrom046
-- name    : OAIQ368Chrom046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:14:57.439475+00:00
-- url     : https://prove2.me/theorems/ae29f102-5289-4cc0-bc7e-002ce828a4c4
-- title:
--   Definitions bundle OAIQ368Chrom046 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 14 definitions, 1 instance and 49 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.ConvolutionQuotient`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.internalDenominator`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.internalNumerator`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.normalizedRightTripleSymbol`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.normalizedTensorSymbol`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.normalizedTripleSymbol`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tensorClearedLeading`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tensorClearedLeadingMap`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tripleClearedLeading`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tripleClearedLeadingMap`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tripleInternalDenominator`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tripleInternalNumerator`, `OAI.ElementaryPositivity.RawShuffle.convolutionIdeal`, `OAI.ElementaryPositivity.RawShuffle.functionalWord`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Shuffle_CoproductIteration`, `Chromatic_Shuffle_GlobalConvolutionQuotient`, `Chromatic_Shuffle_GlobalCoproductCoassociative`, `Chromatic_Shuffle_GlobalShuffleCoalgebra`, `Chromatic_Shuffle_GlobalWordPairing`, `Chromatic_Shuffle_NormalizedTensorSymbol`, `Chromatic_Shuffle_NormalizedTripleSymbol`, `Chromatic_Shuffle_PolynomialExtendInjective`, `Chromatic_Shuffle_SymbolDetection`, `Chromatic_Shuffle_SymbolSwap`, `Chromatic_Shuffle_TensorDivisibility`, `Chromatic_Shuffle_TensorPolynomialBox`, `Chromatic_Shuffle_TensorSymbolSwap`, `Chromatic_Shuffle_TripleAssociativity`, `Chromatic_Shuffle_UnitalCoproductCoassociative`, `Chromatic_Walls_CoproductSymbol`, `Chromatic_Walls_TripleSymbols`, `Chromatic_Walls_UnitalCoproductNaturality`.
--
--   **Imports.** It imports the bundles `OAIQ368Chrom042`, `OAIQ368Chrom043` and `OAIQ368Chrom045` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom047`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom042
import Definitions.Def_OAIQ368Chrom043
import Definitions.Def_OAIQ368Chrom045

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorPolynomialBox
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_center _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.leafVarsEquiv_pack
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

lemma weightComponent_node_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (L R : SplitTree I) (U V : ℤ)
    (x : tensor (quotientFamily a μ) L) (y : tensor (quotientFamily a μ) R)
    (hx : x∈degreeCutSubmodule a μ L U) (hy : y∈degreeCutSubmodule a μ R V) :
    weightComponent a μ (.node L R) (U+V) (x⊗ₜ[ℚ]y)=
      weightComponent a μ L U x ⊗ₜ[ℚ] weightComponent a μ R V y := by
  classical
  apply sub_eq_zero.mp
  apply componentTensor_detect a μ (.node L R)
  rintro ⟨k,l⟩
  rw [map_sub,componentTensor_weightComponent]
  change (if 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=U+V
    then componentTensor a μ L k x⊗ₜ[ℚ]componentTensor a μ R l y else 0)-
    (componentTensor a μ L k (weightComponent a μ L U x)⊗ₜ[ℚ]
      componentTensor a μ R l (weightComponent a μ R V y))=0
  rw [componentTensor_weightComponent,componentTensor_weightComponent]
  by_cases hk : 2*L.totalDegree k+L.doubleShift a<U
  · rw [hx k hk]
    simp
  by_cases hl : 2*R.totalDegree l+R.doubleShift a<V
  · rw [hy l hl]
    simp
  split_ifs <;> (try simp only [TensorProduct.zero_tmul,TensorProduct.tmul_zero,sub_self]) <;> omega

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
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
lemma pairSymmetric_of_slope (a : I → I → ℕ) (c η : I → ℝ) (θ : ℝ)
    (hχ : SlopeEulerSymmetric a c η θ) (T : SplitTree I) (hT : T.OnSlope c η θ) :
    T.PairSymmetric a := by
  intro ij _
  obtain ⟨hi,hsi⟩:=T.leafDimension_onSlope c η θ hT ij.1
  obtain ⟨hj,hsj⟩:=T.leafDimension_onSlope c η θ hT ij.2
  exact hχ _ _ hi hj hsi hsj

end SplitTree

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorDivisibility
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
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma mapLinear_weight_box (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (L R : SplitTree I) (U V : ℤ)
    (p : MvPolynomial L.Centers (tensor (quotientFamily a μ) L))
    (q : MvPolynomial R.Centers (tensor (quotientFamily a μ) R))
    (hp : ∀ z,p.coeff z∈degreeCutSubmodule a μ L U)
    (hq : ∀ z,q.coeff z∈degreeCutSubmodule a μ R V) :
    mapLinear (weightComponent a μ (.node L R) (U+V)) (box p q)=
      box (mapLinear (weightComponent a μ L U) p) (mapLinear (weightComponent a μ R V) q) := by
  ext z
  rw [←Finsupp.comapDomain_sumElim_comapDomain z]
  simp only [coeff_mapLinear,coeff_box]
  exact weightComponent_node_tmul a μ L R U V _ _ (hp _) (hq _)

lemma refinedLeadingPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (U V : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim)
    (y : B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceFiltration a c η hc θ L.dim U)
    (hy : y∈sourceFiltration a c η hc θ R.dim V) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) (U+V))
      (refinedCenterPolynomial a c η hc θ L R hL hR (x⊗ₜ[ℚ]y))=
      box (totalLeadingPolynomial a c η hc θ L hL U x)
        (totalLeadingPolynomial a c η hc θ R hR V y) := by
  rw [refinedCenterPolynomial_tmul]
  exact mapLinear_weight_box a _ L R U V _ _
    (centeredRestrictionB_coeff_degreeCut a c η hc θ L hL U x hx)
    (centeredRestrictionB_coeff_degreeCut a c η hc θ R hR V y hy)

noncomputable def internalDenominator (a : I → I → ℕ) (L R : SplitTree I) :
    MvPolynomial (L.node R).Centers ℚ :=
  rename Sum.inl (centerDenominator a L L.centerPairs)*
  rename Sum.inr (centerDenominator a R R.centerPairs)

noncomputable def internalNumerator (a : I → I → ℕ) (L R : SplitTree I) :
    MvPolynomial (L.node R).Centers ℚ :=
  rename Sum.inl (centerNumerator a L L.centerPairs)*
  rename Sum.inr (centerNumerator a R R.centerPairs)

lemma refinedLeadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (internalDenominator a L R) ∣
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR x) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U,V,x,y,hw,hx,hy,rfl⟩:=hz
    have hy' := sourceFiltration_antitone a c η hc θ R.dim (show W-U≤V by omega) hy
    have he : W=U+(W-U) := by omega
    rw [he,refinedLeadingPolynomial_tmul a c η hc θ L R hL hR U (W-U) x y hx hy']
    obtain ⟨p,hp⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ L hL U x hx
      L.centerPairs L.centerPairs_ne L.centerPairs_norev hχL
    obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ R hR (W-U) y hy'
      R.centerPairs R.centerPairs_ne R.centerPairs_norev hχR
    refine ⟨box p q,?_⟩
    rw [hp,hq,box_scalar_left]
    rfl
  | zero =>
    simp only [refinedCenterPolynomial,map_zero]
    exact dvd_zero _
  | add x y hx hy ihx ihy =>
    simp only [refinedCenterPolynomial,map_add] at ihx ihy ⊢
    exact dvd_add ihx ihy
  | smul r x hx ih =>
    obtain ⟨q,hq⟩:=ih
    refine ⟨r • q,?_⟩
    simp only [refinedCenterPolynomial,map_smul] at hq ⊢
    rw [hq,mul_smul_comm]
end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma centerPairs_prod_node {A : Type*} [CommMonoid A] (L R : SplitTree I)
    (f : (L.node R).Centers × (L.node R).Centers → A) :
    (∏ ij∈(L.node R).centerPairs,f ij)=
      (∏ ij∈L.centerPairs,f (Sum.inl ij.1,Sum.inl ij.2))*
      (∏ ij∈R.centerPairs,f (Sum.inr ij.1,Sum.inr ij.2))*
      (∏ ij∈crossPairs L R,f ij) := by
  classical
  have hLL (x y : L.Centers) :
      @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inl x) (Sum.inl y) ↔ x<y := Sum.lex_inl_inl
  have hRR (x y : R.Centers) :
      @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inr x) (Sum.inr y) ↔ x<y := Sum.lex_inr_inr
  have hLR (x : L.Centers) (y : R.Centers) :
      @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inl x) (Sum.inr y) := Sum.Lex.sep _ _
  have hRL (x : R.Centers) (y : L.Centers) :
      ¬ @LT.lt (L.node R).Centers (centersLinearOrder (L.node R)).toLT
        (Sum.inr x) (Sum.inl y) := Sum.lex_inr_inl
  simp only [centerPairs,Finset.prod_filter,Fintype.prod_prod_type,
    Fintype.prod_sum_type]
  simp only [crossPairs,Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h),
    Fintype.prod_prod_type]
  simp only [hLL,hRR,hLR,hRL,ite_true, if_true,ite_false, if_false,Finset.prod_const_one,one_mul,
    Finset.prod_mul_distrib]
  ac_rfl

omit [DecidableEq I] in
lemma centerNumerator_node (a : I → I → ℕ) (L R : SplitTree I) :
    centerNumerator a (.node L R) (L.node R).centerPairs =
      rename Sum.inl (centerNumerator a L L.centerPairs)*
      rename Sum.inr (centerNumerator a R R.centerPairs)*
      centerNumerator a (.node L R) (crossPairs L R) := by
  unfold centerNumerator
  rw [centerPairs_prod_node]
  simp only [map_prod,map_pow,diagonal,map_sub,rename_X,leafDimension]

omit [DecidableEq I] in
lemma centerDenominator_node (a : I → I → ℕ) (L R : SplitTree I) :
    centerDenominator a (.node L R) (L.node R).centerPairs =
      rename Sum.inl (centerDenominator a L L.centerPairs)*
      rename Sum.inr (centerDenominator a R R.centerPairs)*
      centerDenominator a (.node L R) (crossPairs L R) := by
  unfold centerDenominator
  rw [centerPairs_prod_node]
  simp only [map_prod,map_pow,diagonal,map_sub,rename_X,leafDimension]
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CoproductSymbol
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma centerNumerator_crossPairs_line (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
      (centerNumerator a (L.node R) (crossPairs L R))=
      crossPolynomial a L R v w Int.toNat := by
  classical
  unfold centerNumerator crossPairs
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

lemma refined_leading_zero_factor (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W)
    (q : MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
    (hq : totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f=
      map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (centerDenominator a (L.node R) (crossPairs L R))*q) :
    CenterCalculus.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (refinedCenterPolynomial a c η hc θ L R hL hR
        (separationCoefficient a c η hc
          ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f))=
      map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (centerNumerator a (L.node R) (crossPairs L R))*q := by
  apply eq_of_evalRat
  intro v
  have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr)=v := by
    funext z
    cases z <;> rfl
  have h:=refined_leading_separation_formula a c η hc θ L R hL hR
    (v ∘ Sum.inl) (v ∘ Sum.inr) W f hf
  rw [hq,map_mul,lineSpecialization_map_algebra,centerDenominator_crossPairs_line,
    map_mul,←polynomial_map,←mul_assoc,←map_mul,scalarCrossKernel_denominator,
    polynomial_map] at h
  have hh:=congrArg (fun x : LaurentSeries (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))=>x.coeff (-(0:ℤ))) h
  rw [LaurentAtInfinity.mapLinear_coeff,mapRing_coeff,←map_mul] at hh
  simp only [neg_zero] at hh
  rw [show ∀ p : Polynomial (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)),
    (polynomial p).coeff 0=p.coeff 0 from fun p=>by simpa using polynomial_coeff p 0,
    Polynomial.mul_coeff_zero,Polynomial.coeff_map,
    ←centerNumerator_crossPairs_line,lineSpecialization_coeff_zero,
    lineSpecialization_coeff_zero,hv] at hh
  rw [evalRat_mapLinear,refinedCenterPolynomial_eval,map_mul,evalRat_map_algebra_eq]
  exact hh

theorem coproductSymbol_cross_cleared (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (centerDenominator a (L.node R) (crossPairs L R))*
      CenterCalculus.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR
          (separationCoefficient a c η hc
            ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f))=
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (centerNumerator a (L.node R) (crossPairs L R))*
      totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f := by
  obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ (.node L R) ⟨hL,hR⟩
    W f hf (crossPairs L R) (crossPairs_ne L R) (crossPairs_norev L R)
      (crossPairs_symmetric a c η θ hχ L R hL hR)
  rw [refined_leading_zero_factor a c η hc θ L R hL hR W f hf q hq,hq]
  ring

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_NormalizedTensorSymbol
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open SeparationInfinity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma internalDenominator_ne_zero (a : I → I → ℕ) (L R : SplitTree I) :
    internalDenominator a L R≠0 := by
  apply mul_ne_zero
  · exact fun h=>centerDenominator_ne_zero a L ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerDenominator_ne_zero a R ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

noncomputable def tensorClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  Classical.choose (refinedLeadingPolynomial_denominator_divisible a c η hc θ L R hL hR hχL hχR W f.val f.property)

lemma denominator_tensorClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (internalDenominator a L R)*tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f=
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR f.val) :=
  (Classical.choose_spec (refinedLeadingPolynomial_denominator_divisible a c η hc θ L R hL hR hχL hχR W f.val f.property)).symm

noncomputable def tensorClearedLeadingMap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ) :
    sourceTensorFiltration a c η hc θ L.dim R.dim W →ₗ[ℚ]
      MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  { toFun := tensorClearedLeading a c η hc θ L R hL hR hχL hχR W
    map_add' := by
      intro f g
      apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
      dsimp only
      rw [mul_add,denominator_tensorClearedLeading,denominator_tensorClearedLeading,denominator_tensorClearedLeading]
      simp only [refinedCenterPolynomial,Submodule.coe_add,map_add]
    map_smul' := by
      intro r f
      apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
      dsimp only
      rw [mul_smul_comm,denominator_tensorClearedLeading,denominator_tensorClearedLeading]
      simp only [refinedCenterPolynomial,Submodule.coe_smul,map_smul,RingHom.id_apply] }

noncomputable def normalizedTensorSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ) :
    sourceTensorFiltration a c η hc θ L.dim R.dim W →ₗ[ℚ]
      MvPolynomial (L.node R).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)) :=
  (LinearMap.mulLeft ℚ (map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
    (internalNumerator a L R))).comp (tensorClearedLeadingMap a c η hc θ L R hL hR hχL hχR W)

theorem coproduct_normalized_symbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    normalizedTensorSymbol a c η hc θ L R hL hR
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ R hR) W
      ⟨separationCoefficient a c η hc
        ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f.val,
        separationCoefficient_filtration a c η hc θ L.dim R.dim _ W 0 f.val f.property⟩ =
    normalizedSymbol a c η hc θ (.node L R) ⟨hL,hR⟩
      (pairSymmetric_of_slope a c η θ hχ (.node L R) ⟨hL,hR⟩) W f := by
  let χL := pairSymmetric_of_slope a c η θ hχ L hL
  let χR := pairSymmetric_of_slope a c η θ hχ R hR
  let χT := pairSymmetric_of_slope a c η θ hχ (.node L R) ⟨hL,hR⟩
  let f0 : sourceTensorFiltration a c η hc θ L.dim R.dim W :=
    ⟨separationCoefficient a c η hc
      ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) 0 f.val,
      separationCoefficient_filtration a c η hc θ L.dim R.dim _ W 0 f.val f.property⟩
  have hd := denominator_tensorClearedLeading a c η hc θ L R hL hR χL χR W f0
  have hf := denominator_clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩ χT W f
  have hx := coproductSymbol_cross_cleared a c η hc θ hχ L R hL hR W f.val f.property
  rw [←hd,←hf,centerDenominator_node] at hx
  have he : tensorClearedLeading a c η hc θ L R hL hR χL χR W f0=
      map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (centerNumerator a (.node L R) (crossPairs L R))*
      clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩ χT W f := by
    apply scalar_mul_injective _ (centerDenominator_ne_zero a (.node L R))
    rw [centerDenominator_node]
    change map _ (internalDenominator a L R*centerDenominator a (.node L R) (crossPairs L R))*_=
      map _ (internalDenominator a L R*centerDenominator a (.node L R) (crossPairs L R))*_
    unfold internalDenominator at hx ⊢
    simp only [map_mul] at hx ⊢
    linear_combination hx
  change map _ (internalNumerator a L R)*tensorClearedLeading a c η hc θ L R hL hR χL χR W f0=
    map _ (centerNumerator a (.node L R) (L.node R).centerPairs)*
      clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩ χT W f
  rw [he,centerNumerator_node]
  simp only [internalNumerator,map_mul]
  ring

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma internalNumerator_ne_zero (a : I → I → ℕ) (L R : SplitTree I) :
    internalNumerator a L R≠0 := by
  apply mul_ne_zero
  · exact fun h=>centerNumerator_ne_zero a L ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerNumerator_ne_zero a R ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

lemma normalizedTensorSymbol_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (U V : ℤ)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceFiltration a c η hc θ R.dim V) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR (U+V)
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedSymbol a c η hc θ R hR hχR V y) := by
  let xy : sourceTensorFiltration a c η hc θ L.dim R.dim (U+V) :=
    ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩
  have h : tensorClearedLeading a c η hc θ L R hL hR hχL hχR (U+V) xy=
      box (clearedLeading a c η hc θ L hL hχL U x) (clearedLeading a c η hc θ R hR hχR V y) := by
    apply scalar_mul_injective _ (internalDenominator_ne_zero a L R)
    dsimp only
    rw [denominator_tensorClearedLeading]
    change mapLinear _ (refinedCenterPolynomial a c η hc θ L R hL hR (x.val⊗ₜ[ℚ]y.val))=_
    rw [refinedLeadingPolynomial_tmul a c η hc θ L R hL hR U V x.val y.val x.property y.property,
      ←denominator_clearedLeading a c η hc θ L hL hχL U x,
      ←denominator_clearedLeading a c η hc θ R hR hχR V y,box_scalar_left]
    rfl
  change map _ (internalNumerator a L R)*tensorClearedLeading a c η hc θ L R hL hR hχL hχR (U+V) xy=
    box (map _ (centerNumerator a L L.centerPairs)*clearedLeading a c η hc θ L hL hχL U x)
      (map _ (centerNumerator a R R.centerPairs)*clearedLeading a c η hc θ R hR hχR V y)
  rw [h,box_scalar_left]
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

noncomputable def tripleInternalDenominator (a : I → I → ℕ) (L M N : SplitTree I) :
    MvPolynomial ((L.node M).node N).Centers ℚ :=
  rename Sum.inl (internalDenominator a L M)*rename Sum.inr (centerDenominator a N N.centerPairs)

noncomputable def tripleInternalNumerator (a : I → I → ℕ) (L M N : SplitTree I) :
    MvPolynomial ((L.node M).node N).Centers ℚ :=
  rename Sum.inl (internalNumerator a L M)*rename Sum.inr (centerNumerator a N N.centerPairs)

omit [DecidableEq I] in
lemma tripleInternalDenominator_ne_zero (a : I → I → ℕ) (L M N : SplitTree I) :
    tripleInternalDenominator a L M N≠0 := by
  apply mul_ne_zero
  · exact fun h=>internalDenominator_ne_zero a L M ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerDenominator_ne_zero a N ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

omit [DecidableEq I] in
lemma tripleInternalNumerator_ne_zero (a : I → I → ℕ) (L M N : SplitTree I) :
    tripleInternalNumerator a L M N≠0 := by
  apply mul_ne_zero
  · exact fun h=>internalNumerator_ne_zero a L M ((rename_eq_zero_iff_of_injective _ Sum.inl_injective).mp h)
  · exact fun h=>centerNumerator_ne_zero a N ((rename_eq_zero_iff_of_injective _ Sum.inr_injective).mp h)

lemma refinedTripleLeadingPolynomial_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ) (U V : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)
    (y : B a (SlopeArithmetic.slope c η) N.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim M.dim U)
    (hy : y∈sourceFiltration a c η hc θ N.dim V) :
    mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) (U+V))
      (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN (x⊗ₜ[ℚ]y))=
      box (mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L M) U)
        (refinedCenterPolynomial a c η hc θ L M hL hM x))
        (totalLeadingPolynomial a c η hc θ N hN V y) := by
  rw [refinedTripleCenterPolynomial_tmul]
  exact mapLinear_weight_box a _ (.node L M) N U V _ _
    (refinedCenterPolynomial_coeff_degreeCut a c η hc θ L M hL hM U x hx)
    (centeredRestrictionB_coeff_degreeCut a c η hc θ N hN V y hy)

lemma refinedTripleLeadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) M.dim)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) N.dim)
    (hx : x∈sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
      (tripleInternalDenominator a L M N) ∣
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) W)
        (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN x) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U,V,x,y,hw,hx,hy,rfl⟩:=hz
    have hy' := sourceFiltration_antitone a c η hc θ N.dim (show W-U≤V by omega) hy
    have he : W=U+(W-U) := by omega
    rw [he,refinedTripleLeadingPolynomial_tmul a c η hc θ L M N hL hM hN U (W-U) x y hx hy']
    obtain ⟨p,hp⟩:=refinedLeadingPolynomial_denominator_divisible a c η hc θ L M hL hM hχL hχM U x hx
    obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ N hN (W-U) y hy'
      N.centerPairs N.centerPairs_ne N.centerPairs_norev hχN
    refine ⟨box p q,?_⟩
    rw [hp,hq,box_scalar_left]
    rfl
  | zero =>
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_zero,LinearMap.map_zero]
    exact dvd_zero _
  | add x y hx hy ihx ihy =>
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_add,LinearMap.map_add]
    exact dvd_add ihx ihy
  | smul r x hx ih =>
    obtain ⟨q,hq⟩:=ih
    refine ⟨r • q,?_⟩
    rw [(refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN).map_smul r x,
      LinearMap.map_smul,hq,mul_smul_comm]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_NormalizedTripleSymbol
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def tripleClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (f : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    MvPolynomial ((L.node M).node N).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  Classical.choose (refinedTripleLeadingPolynomial_denominator_divisible a c η hc θ L M N hL hM hN hχL hχM hχN W f.val f.property)

lemma denominator_tripleClearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (f : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
      (tripleInternalDenominator a L M N)*tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W f=
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) W)
        (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN f.val) :=
  (Classical.choose_spec (refinedTripleLeadingPolynomial_denominator_divisible a c η hc θ L M N hL hM hN hχL hχM hχN W f.val f.property)).symm

noncomputable def tripleClearedLeadingMap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ) :
    sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W →ₗ[ℚ]
      MvPolynomial ((L.node M).node N).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  { toFun := tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W
    map_add' := by
      intro f g
      apply scalar_mul_injective _ (tripleInternalDenominator_ne_zero a L M N)
      dsimp only
      rw [mul_add,denominator_tripleClearedLeading,denominator_tripleClearedLeading,denominator_tripleClearedLeading]
      simp only [Submodule.coe_add,LinearMap.map_add]
    map_smul' := by
      intro r f
      apply scalar_mul_injective _ (tripleInternalDenominator_ne_zero a L M N)
      dsimp only
      rw [mul_smul_comm,denominator_tripleClearedLeading,denominator_tripleClearedLeading]
      simp only [Submodule.coe_smul,LinearMap.map_smul,RingHom.id_apply] }

noncomputable def normalizedTripleSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ) :
    sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W →ₗ[ℚ]
      MvPolynomial ((L.node M).node N).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)) :=
  (LinearMap.mulLeft ℚ (map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
    (tripleInternalNumerator a L M N))).comp (tripleClearedLeadingMap a c η hc θ L M N hL hM hN hχL hχM hχN W)

lemma normalizedTripleSymbol_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (U V : ℤ)
    (x : sourceTensorFiltration a c η hc θ L.dim M.dim U)
    (y : sourceFiltration a c η hc θ N.dim V) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V)
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩=
      box (normalizedTensorSymbol a c η hc θ L M hL hM hχL hχM U x)
        (normalizedSymbol a c η hc θ N hN hχN V y) := by
  let xy : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim (U+V) :=
    ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,le_refl _,x.property,y.property,rfl⟩⟩
  have h : tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN (U+V) xy=
      box (tensorClearedLeading a c η hc θ L M hL hM hχL hχM U x) (clearedLeading a c η hc θ N hN hχN V y) := by
    apply scalar_mul_injective _ (tripleInternalDenominator_ne_zero a L M N)
    dsimp only
    rw [denominator_tripleClearedLeading]
    change mapLinear _ (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN (x.val⊗ₜ[ℚ]y.val))=_
    rw [refinedTripleLeadingPolynomial_tmul a c η hc θ L M N hL hM hN U V x.val y.val x.property y.property,
      ←denominator_tensorClearedLeading a c η hc θ L M hL hM hχL hχM U x,
      ←denominator_clearedLeading a c η hc θ N hN hχN V y,box_scalar_left]
    rfl
  change map _ (tripleInternalNumerator a L M N)*tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN (U+V) xy=
    box (map _ (internalNumerator a L M)*tensorClearedLeading a c η hc θ L M hL hM hχL hχM U x)
      (map _ (centerNumerator a N N.centerPairs)*clearedLeading a c η hc θ N hN hχN V y)
  rw [h,box_scalar_left]
  rfl

lemma normalizedTripleSymbol_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ)
    (f : sourceTripleFiltration a c η hc θ L.dim M.dim N.dim W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W f=0 ↔
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) ((L.node M).node N) W)
        (refinedTripleCenterPolynomial a c η hc θ L M N hL hM hN f.val)=0 := by
  change map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) ((L.node M).node N)))
    (tripleInternalNumerator a L M N)*tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W f=0 ↔ _
  rw [SymbolCoordinates.scalar_mul_eq_zero_iff _ (tripleInternalNumerator_ne_zero a L M N)]
  rw [←denominator_tripleClearedLeading a c η hc θ L M N hL hM hN hχL hχM hχN W f,
    SymbolCoordinates.scalar_mul_eq_zero_iff _ (tripleInternalDenominator_ne_zero a L M N)]

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem normalizedTripleSymbol_detect (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (W : ℤ) (x : sourceTripleFiltration a c η hc θ d e f W)
    (h : ∀ (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
      (hN : N.OnSlope c η θ) (hd : L.dim=d) (he : M.dim=e) (hf : N.dim=f),
      normalizedTripleSymbol a c η hc θ L M N hL hM hN
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
        (pairSymmetric_of_slope a c η θ hχ N hN) W (hd ▸ he ▸ hf ▸ x)=0) :
    x.val∈sourceTripleFiltration a c η hc θ d e f (W+1) := by
  apply triple_leading_restrictions_detect a c η hc θ d e f W x.val x.property
  rintro ⟨L,hoL,hL,hd,k,z⟩ ⟨M,hoM,hM,he,l,w⟩ ⟨N,hoN,hN,hf,m,t⟩ hw
  subst d
  subst e
  subst f
  have hp := (normalizedTripleSymbol_eq_zero_iff a c η hc θ L M N hL hM hN _ _ _ W x).mp
    (h L M N hL hM hN rfl rfl rfl)
  have ht := congrArg (fun p=>componentTensor a (SlopeArithmetic.slope c η) ((L.node M).node N) ((k,l),m)
    (MvPolynomial.coeff ((z.sumElim w).sumElim t) p)) hp
  have heq : 2*((L.totalDegree k+M.totalDegree l)+N.totalDegree m)+
      ((L.doubleShift a+M.doubleShift a)+N.doubleShift a)=W := by
    change (2*L.totalDegree k+L.doubleShift a)+(2*M.totalDegree l+M.doubleShift a)+
      (2*N.totalDegree m+N.doubleShift a)=W at hw
    omega
  rw [coeff_mapLinear,componentTensor_weightComponent,ite_eq_left heq,
    MvPolynomial.coeff_zero,LinearMap.map_zero,
    refinedTripleCenterPolynomial_coeff_test] at ht
  exact ht

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma centerPower_node (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ) :
    centerPower a (L.node R) φ = rename Sum.inl (centerPower a L φ)*
      rename Sum.inr (centerPower a R φ)*crossPower a L R φ := by
  unfold centerPower
  rw [centerPairs_prod_node]
  simp only [crossPairs,Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h),
    Fintype.prod_prod_type,map_prod,map_pow,diagonal,map_sub,rename_X,leafDimension,crossPower]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorSymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma normalizedTensorSymbol_tmul_eq (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W U V : ℤ) (hw : W=U+V)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceFiltration a c η hc θ R.dim V) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,hw.le,x.property,y.property,rfl⟩⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedSymbol a c η hc θ R hR hχR V y) := by
  subst W
  exact normalizedTensorSymbol_tmul a c η hc θ L R hL hR hχL hχR U V x y

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CoproductIteration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus

lemma normalizedTripleSymbol_tmul_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a)
    (W U V : ℤ) (hw : W=U+V)
    (x : sourceTensorFiltration a c η hc θ L.dim M.dim U)
    (y : sourceFiltration a c η hc θ N.dim V) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,hw.le,x.property,y.property,rfl⟩⟩=
      box (normalizedTensorSymbol a c η hc θ L M hL hM hχL hχM U x)
        (normalizedSymbol a c η hc θ N hN hχN V y) := by
  subst W
  exact normalizedTripleSymbol_tmul a c η hc θ L M N hL hM hN hχL hχM hχN U V x y

theorem tensorSeparationLeft_normalized_symbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ) (W : ℤ)
    (x : sourceTensorFiltration a c η hc θ (L.dim+M.dim) N.dim W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (tensorSeparationLeft a c η hc θ L.dim M.dim N.dim
        ((slope_dim c η hc hL).trans (slope_dim c η hc hM).symm) W x)=
      normalizedTensorSymbol a c η hc θ (.node L M) N ⟨hL,hM⟩ hN
        (pairSymmetric_of_slope a c η θ hχ (.node L M) ⟨hL,hM⟩)
        (pairSymmetric_of_slope a c η θ hχ N hN) W x := by
  let hLM := (slope_dim c η hc hL).trans (slope_dim c η hc hM).symm
  let χL:=pairSymmetric_of_slope a c η θ hχ L hL
  let χM:=pairSymmetric_of_slope a c η θ hχ M hM
  let χN:=pairSymmetric_of_slope a c η θ hχ N hN
  let χLM:=pairSymmetric_of_slope a c η θ hχ (.node L M) ⟨hL,hM⟩
  let F:=(normalizedTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W).comp
    (tensorSeparationLeft a c η hc θ L.dim M.dim N.dim hLM W)
  let G:=normalizedTensorSymbol a c η hc θ (.node L M) N ⟨hL,hM⟩ hN χLM χN W
  have he : F=G := by
    apply linearMap_span_ext
    rintro _ ⟨u,v,p,q,huv,hp,hq,rfl⟩
    have hq' := sourceFiltration_antitone a c η hc θ N.dim (show W-u≤v by omega) hq
    let p0:=separationCoefficientRestricted a c η hc θ L.dim M.dim hLM u 0 ⟨p,hp⟩
    have hp0:=normalizedTripleSymbol_tmul_eq a c η hc θ L M N hL hM hN χL χM χN
      W u (W-u) (by omega) p0 ⟨q,hq'⟩
    change normalizedTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W
      ⟨p0.val⊗ₜ[ℚ]q,_⟩=G ⟨p⊗ₜ[ℚ]q,_⟩
    rw [hp0]
    have hp1:=coproduct_normalized_symbol a c η hc θ hχ L M hL hM u ⟨p,hp⟩
    have hp2:=normalizedTensorSymbol_tmul_eq a c η hc θ (.node L M) N ⟨hL,hM⟩ hN χLM χN
      W u (W-u) (by omega) ⟨p,hp⟩ ⟨q,hq'⟩
    change box (normalizedTensorSymbol a c η hc θ L M hL hM χL χM u p0)
      (normalizedSymbol a c η hc θ N hN χN (W-u) ⟨q,hq'⟩)=_
    change normalizedTensorSymbol a c η hc θ L M hL hM χL χM u p0=
      normalizedSymbol a c η hc θ (.node L M) ⟨hL,hM⟩ χLM u ⟨p,hp⟩ at hp1
    rw [hp1]
    exact hp2.symm
  exact LinearMap.congr_fun he x

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TripleAssociativity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def normalizedRightTripleSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (W : ℤ) :
    additiveTensorFiltration (sourceFiltration a c η hc θ L.dim)
      (sourceTensorFiltration a c η hc θ M.dim N.dim) W →ₗ[ℚ]
      MvPolynomial (L.node (M.node N)).Centers
        (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (L.node (M.node N))) :=
  ((extendPolynomial ((Regroup.assoc L M N).equivalence
      (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom (Regroup.assoc L M N).centers).toLinearMap.comp
    (normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W)).comp
    (tensorFiltrationAssoc (sourceFiltration a c η hc θ L.dim) (sourceFiltration a c η hc θ M.dim)
      (sourceFiltration a c η hc θ N.dim) W).symm.toLinearMap

lemma normalizedRightTripleSymbol_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a) (U V : ℤ)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceTensorFiltration a c η hc θ M.dim N.dim V) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V)
      ⟨x.val⊗ₜ[ℚ]y.val,tmul_mem_additiveTensorFiltration _ _ (le_refl _) x.property y.property⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V y) := by
  let E := (extendPolynomial ((Regroup.assoc L M N).equivalence
    (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom (Regroup.assoc L M N).centers).toLinearMap
  let F := (E.comp (normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V))).comp
    (unassocTensorFixedLeft (sourceFiltration a c η hc θ L.dim) (sourceFiltration a c η hc θ M.dim)
      (sourceFiltration a c η hc θ N.dim) U V x)
  let G := (boxRightLinear (normalizedSymbol a c η hc θ L hL hχL U x)).comp
    (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V)
  have he : F=G := by
    apply linearMap_span_ext
    rintro _ ⟨s,t,p,q,hst,hp,hq,rfl⟩
    have hq' := sourceFiltration_antitone a c η hc θ N.dim (show V-s≤t by omega) hq
    let xp : sourceTensorFiltration a c η hc θ L.dim M.dim (U+s) :=
      ⟨x.val⊗ₜ[ℚ]p,tmul_mem_additiveTensorFiltration _ _ (le_refl _) x.property hp⟩
    have h1 := normalizedTripleSymbol_tmul_eq a c η hc θ L M N hL hM hN hχL hχM hχN
      (U+V) (U+s) (V-s) (by omega) xp ⟨q,hq'⟩
    have h2 := normalizedTensorSymbol_tmul a c η hc θ L M hL hM hχL hχM U s x ⟨p,hp⟩
    have h3 := normalizedTensorSymbol_tmul_eq a c η hc θ M N hM hN hχM hχN
      V s (V-s) (by omega) ⟨p,hp⟩ ⟨q,hq'⟩
    change E (normalizedTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN (U+V)
      ⟨(x.val⊗ₜ[ℚ]p)⊗ₜ[ℚ]q,_⟩)=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V ⟨p⊗ₜ[ℚ]q,_⟩)
    rw [h1,h3]
    change E (box (normalizedTensorSymbol a c η hc θ L M hL hM hχL hχM (U+s)
      ⟨x.val⊗ₜ[ℚ]p,_⟩) _)=_
    rw [h2]
    exact box_assoc _ _ _
  exact LinearMap.congr_fun he y

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus

lemma normalizedRightTripleSymbol_tmul_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L M N : SplitTree I)
    (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ) (hN : N.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχM : M.PairSymmetric a) (hχN : N.PairSymmetric a)
    (W U V : ℤ) (hw : W=U+V)
    (x : sourceFiltration a c η hc θ L.dim U)
    (y : sourceTensorFiltration a c η hc θ M.dim N.dim V) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN hχL hχM hχN W
      ⟨x.val⊗ₜ[ℚ]y.val,Submodule.subset_span ⟨U,V,x.val,y.val,hw.le,x.property,y.property,rfl⟩⟩=
      box (normalizedSymbol a c η hc θ L hL hχL U x)
        (normalizedTensorSymbol a c η hc θ M N hM hN hχM hχN V y) := by
  subst W
  exact normalizedRightTripleSymbol_tmul a c η hc θ L M N hL hM hN hχL hχM hχN U V x y

 theorem tensorSeparationRight_normalized_symbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ) (W : ℤ)
    (x : sourceTensorFiltration a c η hc θ L.dim (M.dim+N.dim) W) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (tensorSeparationRight a c η hc θ L.dim M.dim N.dim
        ((slope_dim c η hc hM).trans (slope_dim c η hc hN).symm) W x)=
      normalizedTensorSymbol a c η hc θ L (.node M N) hL ⟨hM,hN⟩
        (pairSymmetric_of_slope a c η θ hχ L hL)
        (pairSymmetric_of_slope a c η θ hχ (.node M N) ⟨hM,hN⟩) W x := by
  let hMN := (slope_dim c η hc hM).trans (slope_dim c η hc hN).symm
  let χL:=pairSymmetric_of_slope a c η θ hχ L hL
  let χM:=pairSymmetric_of_slope a c η θ hχ M hM
  let χN:=pairSymmetric_of_slope a c η θ hχ N hN
  let χMN:=pairSymmetric_of_slope a c η θ hχ (.node M N) ⟨hM,hN⟩
  let F:=(normalizedRightTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W).comp
    (tensorSeparationRight a c η hc θ L.dim M.dim N.dim hMN W)
  let G:=normalizedTensorSymbol a c η hc θ L (.node M N) hL ⟨hM,hN⟩ χL χMN W
  have he : F=G := by
    apply linearMap_span_ext
    rintro _ ⟨u,v,p,q,huv,hp,hq,rfl⟩
    have hq' := sourceFiltration_antitone a c η hc θ (M.dim+N.dim) (show W-u≤v by omega) hq
    let q0:=separationCoefficientRestricted a c η hc θ M.dim N.dim hMN (W-u) 0 ⟨q,hq'⟩
    have hp0:=normalizedRightTripleSymbol_tmul_eq a c η hc θ L M N hL hM hN χL χM χN
      W u (W-u) (by omega) ⟨p,hp⟩ q0
    change normalizedRightTripleSymbol a c η hc θ L M N hL hM hN χL χM χN W
      ⟨p⊗ₜ[ℚ]q0.val,_⟩=G ⟨p⊗ₜ[ℚ]q,_⟩
    rw [hp0]
    have hq1:=coproduct_normalized_symbol a c η hc θ hχ M N hM hN (W-u) ⟨q,hq'⟩
    have hp2:=normalizedTensorSymbol_tmul_eq a c η hc θ L (.node M N) hL ⟨hM,hN⟩ χL χMN
      W u (W-u) (by omega) ⟨p,hp⟩ ⟨q,hq'⟩
    change box (normalizedSymbol a c η hc θ L hL χL u ⟨p,hp⟩)
      (normalizedTensorSymbol a c η hc θ M N hM hN χM χN (W-u) q0)=_
    change normalizedTensorSymbol a c η hc θ M N hM hN χM χN (W-u) q0=
      normalizedSymbol a c η hc θ (.node M N) ⟨hM,hN⟩ χMN (W-u) ⟨q,hq'⟩ at hq1
    rw [hq1]
    exact hp2.symm
  exact LinearMap.congr_fun he x

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PolynomialExtendInjective
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.pairAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tripleAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tripleFilterAdd
lemma normalizedTripleSymbol_difference_mem (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (W : ℤ) (x y : sourceTripleFiltration a c η hc θ d e f W)
    (h : ∀ (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
      (hN : N.OnSlope c η θ) (hd : L.dim=d) (he : M.dim=e) (hf : N.dim=f),
      normalizedTripleSymbol a c η hc θ L M N hL hM hN
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
        (pairSymmetric_of_slope a c η θ hχ N hN) W (hd ▸ he ▸ hf ▸ x)=
      normalizedTripleSymbol a c η hc θ L M N hL hM hN
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
        (pairSymmetric_of_slope a c η θ hχ N hN) W (hd ▸ he ▸ hf ▸ y)) :
    ((x-y : sourceTripleFiltration a c η hc θ d e f W)).val∈sourceTripleFiltration a c η hc θ d e f (W+1) := by
  apply normalizedTripleSymbol_detect a c η hc θ hχ d e f W (x-y)
  intro L M N hL hM hN hd he hf
  subst d
  subst e
  subst f
  rw [LinearMap.map_sub,h L M N hL hM hN rfl rfl rfl,sub_self]

end SplitTree
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma iteratedCoproductLeft_normalizedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ)
    (hde : SlopeArithmetic.slope c η L.dim=SlopeArithmetic.slope c η M.dim)
    (hef : SlopeArithmetic.slope c η M.dim=SlopeArithmetic.slope c η N.dim)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((L.dim+M.dim)+N.dim) W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (iteratedCoproductLeft a c η hc θ L.dim M.dim N.dim hde hef W x)=
    normalizedSymbol a c η hc θ ((L.node M).node N) ⟨⟨hL,hM⟩,hN⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨⟨hL,hM⟩,hN⟩) W x := by
  change normalizedTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
    (tensorSeparationLeft a c η hc θ L.dim M.dim N.dim hde W
      (separationCoefficientRestricted a c η hc θ (L.dim+M.dim) N.dim _ W 0 x))=_
  rw [tensorSeparationLeft_normalized_symbol a c η hc θ hχ L M N hL hM hN W]
  exact coproduct_normalized_symbol a c η hc θ hχ (.node L M) N ⟨hL,hM⟩ hN W x

lemma iteratedCoproductRight_normalizedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ)
    (hde : SlopeArithmetic.slope c η L.dim=SlopeArithmetic.slope c η M.dim)
    (hef : SlopeArithmetic.slope c η M.dim=SlopeArithmetic.slope c η N.dim)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((L.dim+M.dim)+N.dim) W) :
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (iteratedCoproductRight a c η hc θ L.dim M.dim N.dim hde hef W x)=
    normalizedSymbol a c η hc θ (L.node (M.node N)) ⟨hL,⟨hM,hN⟩⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,⟨hM,hN⟩⟩) W
      (filtrationDimensionEquiv a c η hc θ (add_assoc L.dim M.dim N.dim) W x) := by
  change normalizedRightTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
    (tensorSeparationRight a c η hc θ L.dim M.dim N.dim hef W
      (separationCoefficientRestricted a c η hc θ L.dim (M.dim+N.dim) _ W 0
        (filtrationDimensionEquiv a c η hc θ (add_assoc L.dim M.dim N.dim) W x)))=_
  rw [tensorSeparationRight_normalized_symbol a c η hc θ hχ L M N hL hM hN W]
  exact coproduct_normalized_symbol a c η hc θ hχ L (.node M N) hL ⟨hM,hN⟩ W _

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.LinearDetection ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] pairAdd tripleAdd tripleFilterAdd

namespace SplitTree
lemma iteratedCoproduct_normalizedSymbol_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L M N : SplitTree I) (hL : L.OnSlope c η θ) (hM : M.OnSlope c η θ)
    (hN : N.OnSlope c η θ)
    (hde : SlopeArithmetic.slope c η L.dim=SlopeArithmetic.slope c η M.dim)
    (hef : SlopeArithmetic.slope c η M.dim=SlopeArithmetic.slope c η N.dim)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((L.dim+M.dim)+N.dim) W) :
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      (iteratedCoproductLeft a c η hc θ L.dim M.dim N.dim hde hef W x)=
    normalizedTripleSymbol a c η hc θ L M N hL hM hN
      (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ M hM)
      (pairSymmetric_of_slope a c η θ hχ N hN) W
      ((sourceTripleAssoc a c η hc θ L.dim M.dim N.dim W).symm
        (iteratedCoproductRight a c η hc θ L.dim M.dim N.dim hde hef W x)) := by
  apply extendPolynomial_injective
    ((Regroup.assoc L M N).equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
    (Regroup.assoc L M N).centers
    ((Regroup.assoc L M N).equivalence _).injective (Regroup.assoc L M N).centers.injective
  change extendPolynomial _ _ (normalizedTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
    (iteratedCoproductLeft a c η hc θ L.dim M.dim N.dim hde hef W x))=
    normalizedRightTripleSymbol a c η hc θ L M N hL hM hN _ _ _ W
      (iteratedCoproductRight a c η hc θ L.dim M.dim N.dim hde hef W x)
  rw [iteratedCoproductLeft_normalizedSymbol a c η hc θ hχ L M N hL hM hN hde hef W x,
    iteratedCoproductRight_normalizedSymbol a c η hc θ hχ L M N hL hM hN hde hef W x]
  exact (Regroup.normalizedSymbol_natural a c η hc θ (.assoc L M N)
    (Regroup.assoc_orderPreserving L M N) ⟨⟨hL,hM⟩,hN⟩ ⟨hL,⟨hM,hN⟩⟩
    (pairSymmetric_of_slope a c η θ hχ _ ⟨⟨hL,hM⟩,hN⟩)
    (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,⟨hM,hN⟩⟩) W x).symm
end SplitTree

theorem separation_coassoc_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ)
    (hde : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hef : SlopeArithmetic.slope c η e=SlopeArithmetic.slope c η f)
    (W : ℤ) (x : sourceFiltration a c η hc θ ((d+e)+f) W) :
    (iteratedCoproductLeft a c η hc θ d e f hde hef W x -
      (sourceTripleAssoc a c η hc θ d e f W).symm
        (iteratedCoproductRight a c η hc θ d e f hde hef W x)).val∈
      sourceTripleFiltration a c η hc θ d e f (W+1) := by
  apply SplitTree.normalizedTripleSymbol_difference_mem a c η hc θ hχ d e f W
  intro L M N hL hM hN hd he hf
  subst d
  subst e
  subst f
  exact SplitTree.iteratedCoproduct_normalizedSymbol_eq a c η hc θ hχ L M N hL hM hN hde hef W x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_UnitalCoproductNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] unitalSepTensor unitalSepTensorA

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTensorAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTensorModule
lemma unitalCoproduct_coassoc_zero_middle (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d f : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (hf : OnSlopeOrZero c η θ f)
    (x : B a (slope c η) ((d+0)+f)) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl))) LinearMap.id
        (unitalSeparationConstant a c η hc (d+0) f
          ((hd.add hc (Or.inl rfl)).compatible hf) x))=
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc 0 f (Or.inl rfl))
        (unitalSeparationConstant a c η hc d (0+f)
          (hd.compatible ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc hf))
          (castB a (slope c η) (add_assoc d 0 f) x)) := by
  have hL := TensorTransport.map_middle_left
    (unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl)))
    (castBLinear a (slope c η) (add_zero d)) (1:B a (slope c η) 0)
    (fun y=>by rw [castBLinear_apply]; exact unitalSeparationConstant_zero_right_any a c η hc d y)
    (unitalSeparationConstant a c η hc (d+0) f ((hd.add hc (Or.inl rfl)).compatible hf) x)
  have hR := TensorTransport.map_middle_right
    (unitalSeparationConstant a c η hc 0 f (Or.inl rfl))
    (castBLinear a (slope c η) (zero_add f)) (1:B a (slope c η) 0)
    (fun y=>by rw [castBLinear_apply]; exact unitalSeparationConstant_zero_left_any a c η hc f y)
    (unitalSeparationConstant a c η hc d (0+f)
      (hd.compatible ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc hf))
      (castB a (slope c η) (add_assoc d 0 f) x))
  rw [hL,hR]
  have hL' := unitalSeparationConstant_cast a c η hc (add_zero d) (rfl : f=f)
    ((hd.add hc (Or.inl rfl)).compatible hf) (hd.compatible hf) x
  have hR' := unitalSeparationConstant_cast a c η hc (rfl : d=d) (zero_add f)
    (hd.compatible ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc hf))
    (hd.compatible hf) (castB a (slope c η) (add_assoc d 0 f) x)
  simp only [castBLinear_rfl] at hL' hR' ⊢
  rw [←hL',←hR',castB_trans]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalTripleRightAdd
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalTripleRightModule
theorem unitalCoproduct_coassoc_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (he : OnSlopeOrZero c η θ e) (hf : OnSlopeOrZero c η θ f)
    (W : ℤ) (x : B a (slope c η) ((d+e)+f))
    (hx : x∈unitalSourceFiltration a c η hc θ ((d+e)+f) W) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
        (unitalSeparationConstant a c η hc (d+e) f ((hd.add hc he).compatible hf) x)) -
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc d (e+f) (hd.compatible (he.add hc hf))
          (castB a (slope c η) (add_assoc d e f) x)) ∈
      additiveTensorFiltration (unitalSourceFiltration a c η hc θ d)
        (unitalSourceTensorFiltration a c η hc θ e f) (W+1) := by
  by_cases hd0 : d=0
  · subst d
    rw [unitalCoproduct_coassoc_zero_left a c η hc θ e f he hf x,sub_self]
    exact Submodule.zero_mem _
  by_cases he0 : e=0
  · subst e
    rw [unitalCoproduct_coassoc_zero_middle a c η hc θ d f hd hf x,sub_self]
    exact Submodule.zero_mem _
  by_cases hf0 : f=0
  · subst f
    rw [unitalCoproduct_coassoc_zero_right a c η hc θ d e hd he x,sub_self]
    exact Submodule.zero_mem _
  have hde : slope c η d=slope c η e := (hd.resolve_left hd0).trans (he.resolve_left he0).symm
  have hef : slope c η e=slope c η f := (he.resolve_left he0).trans (hf.resolve_left hf0).symm
  have hdef : slope c η (d+e)=slope c η f := (slope_add_same c η hc hde).trans (hde.trans hef)
  have hdef' : slope c η d=slope c η (e+f) := hde.trans (slope_add_same c η hc hef).symm
  rw [unitalSourceFiltration_nonzero a c η hc θ ((d+e)+f)
    (add_ne_zero_left _ _ (add_ne_zero_left _ _ hd0)) W] at hx
  have hm := separation_coassoc_filtration a c η hc θ hχ d e f hde hef W ⟨x,hx⟩
  have hm' := assoc_mem_tensorFiltration (sourceFiltration a c η hc θ d)
    (sourceFiltration a c η hc θ e) (sourceFiltration a c η hc θ f) (W+1) _ hm
  change TensorProduct.assoc ℚ _ _ _
    ((iteratedCoproductLeft a c η hc θ d e f hde hef W ⟨x,hx⟩).val -
      (TensorProduct.assoc ℚ _ _ _).symm
        (iteratedCoproductRight a c η hc θ d e f hde hef W ⟨x,hx⟩).val) ∈ _ at hm'
  rw [TensorTransport.assoc_sub_symm] at hm'
  rw [show unitalSourceFiltration a c η hc θ d=sourceFiltration a c η hc θ d from
      funext (unitalSourceFiltration_nonzero a c η hc θ d hd0),
    show unitalSourceTensorFiltration a c η hc θ e f=sourceTensorFiltration a c η hc θ e f from
      funext (unitalSourceTensorFiltration_nonzero a c η hc θ e f he0 hf0),
    unitalSeparationConstant_eq_linear a c η hc d e _ hde,
    unitalSeparationConstant_eq_linear a c η hc e f _ hef,
    unitalSeparationConstant_eq_linear a c η hc (d+e) f _ hdef,
    unitalSeparationConstant_eq_linear a c η hc d (e+f) _ hdef']
  change TensorProduct.assoc ℚ _ _ _
    (TensorProduct.map (separationCoefficient a c η hc hde 0) LinearMap.id
      (separationCoefficient a c η hc hdef 0 x)) -
    TensorProduct.map LinearMap.id (separationCoefficient a c η hc hef 0)
      (separationCoefficient a c η hc hdef' 0
        (filtrationDimensionEquiv a c η hc θ (add_assoc d e f) W ⟨x,hx⟩).val)∈_ at hm'
  rw [filtrationDimensionEquiv_castB] at hm'
  exact hm'

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
  ElementaryPositivity.LinearFiltration SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] naturalTensorAdd naturalTensorModule pairAdd tripleAdd tripleFilterAdd
  unitalTripleRightAdd unitalTripleRightModule

theorem unitalGradeCoproduct_coassociative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e f : I → ℕ) (hd : OnSlopeOrZero c η θ d)
    (he : OnSlopeOrZero c η θ e) (hf : OnSlopeOrZero c η θ f)
    (W : ℤ) (x : UnitalSourceGrade a c η hc θ ((d+e)+f) W) :
    tensorGradeAssoc (unitalSourceFiltration a c η hc θ d)
      (unitalSourceFiltration a c η hc θ e) (unitalSourceFiltration a c η hc θ f) W
      (unitalTensorCoproductLeft a c η hc θ d e f (hd.compatible he) W
        (unitalGradeCoproduct a c η hc θ (d+e) f ((hd.add hc he).compatible hf) W x))=
      unitalTensorCoproductRight a c η hc θ d e f (he.compatible hf) W
        (unitalGradeCoproduct a c η hc θ d (e+f) (hd.compatible (he.add hc hf)) W
          (unitalGradeCast a c η hc θ (add_assoc d e f) rfl x)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [unitalGradeCast_mk,unitalGradeCoproduct_mk,unitalGradeCoproduct_mk]
    apply sub_eq_zero.mp
    change mk _ _ ⟨TensorProduct.assoc ℚ _ _ _
        (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
          (unitalSeparationConstant a c η hc (d+e) f ((hd.add hc he).compatible hf) x.val)),_⟩ -
      mk _ _ ⟨TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc d (e+f) (hd.compatible (he.add hc hf))
          (unitalFiltrationCast a c η hc θ (add_assoc d e f) rfl x).val),_⟩=0
    rw [←LinearMap.map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change TensorProduct.assoc ℚ _ _ _
        (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
          (unitalSeparationConstant a c η hc (d+e) f ((hd.add hc he).compatible hf) x.val)) -
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc d (e+f) (hd.compatible (he.add hc hf))
          (unitalFiltrationCast a c η hc θ (add_assoc d e f) rfl x).val)∈
      additiveTensorFiltration (unitalSourceFiltration a c η hc θ d)
        (unitalSourceTensorFiltration a c η hc θ e f) (W+1)
    rw [unitalFiltrationCast_val]
    exact unitalCoproduct_coassoc_filtration a c η hc θ hχ d e f hd he hf W x.val x.property
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalTripleCoproduct_left_explicit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (globalTripleGradeLeft a c η hc θ ⟨p.val.1,p.property.2.1⟩
        ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ k.2
        (unitalTensorCoproductLeft a c η hc θ p.val.1 p.val.2.1 p.val.2.2
          (p.property.2.1.compatible p.property.2.2.1) k.2
          (unitalGradeCoproduct a c η hc θ (p.val.1+p.val.2.1) p.val.2.2
            ((p.property.2.1.add hc p.property.2.2.1).compatible p.property.2.2.2) k.2
            (unitalGradeCast a c η hc θ p.property.1.symm rfl x))))=
      globalTripleCoproduct a c η hc θ k p x := by
  have H := unitalGradeCoproduct_coassociative a c η hc θ hχ
    p.val.1 p.val.2.1 p.val.2.2 p.property.2.1 p.property.2.2.1 p.property.2.2.2
    k.2 (unitalGradeCast a c η hc θ p.property.1.symm rfl x)
  have HH := congrArg (globalTripleGradeRight a c η hc θ ⟨p.val.1,p.property.2.1⟩
    ⟨p.val.2.1,p.property.2.2.1⟩ ⟨p.val.2.2,p.property.2.2.2⟩ k.2) H
  rw [globalTripleGrade_assoc] at HH
  rw [unitalGradeCast_trans] at HH
  exact HH

lemma globalTripleCoproduct_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalLeftTripleCoproduct a c η hc θ k p x=
      globalTripleCoproduct a c η hc θ k p x := by
  dsimp only [globalLeftTripleCoproduct,globalLeftTripleOutput]
  exact globalTripleCoproduct_left_explicit a c η hc θ hχ k p x

lemma globalIteratedLeftSplit_build (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : SlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (globalIteratedLeftSplit a c η hc θ k (leftTripleBuild c η hc θ k.1.val p).1
        (leftTripleBuild c η hc θ k.1.val p).2 x)=
      globalTripleCoproduct a c η hc θ k p x := by
  exact (globalIteratedLeftSplit_build_left a c η hc θ k p x).trans
    (globalTripleCoproduct_left a c η hc θ hχ k p x)

lemma globalIteratedLeftSplit_view (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (p : LeftSlopeTriple c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _ (globalIteratedLeftSplit a c η hc θ k p.1 p.2 x)=
      globalTripleCoproduct a c η hc θ k (leftTripleView c η hc θ k.1.val p) x := by
  have hh := globalIteratedLeftSplit_build a c η hc θ hχ k
    (leftTripleView c η hc θ k.1.val p) x
  rw [leftTripleBuild_view] at hh
  exact hh

lemma globalIteratedLeft_sum (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (left s.val),
        globalIteratedLeftSplit a c η hc θ k s t x)=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (left s.val),
        globalTripleCoproduct a c η hc θ k (leftTripleView c η hc θ k.1.val ⟨s,t⟩) x := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact globalIteratedLeftSplit_view a c η hc θ hχ k ⟨s,t⟩ x

lemma globalCoproduct_coassociative_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)))=
      TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ)
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)) := by
  rw [globalCoproduct_iterated_left_lof,globalCoproduct_iterated_right_lof,
    globalIteratedLeft_sum a c η hc θ hχ,globalIteratedRight_sum]
  exact sum_slopeTriple c η hc θ k.1.val (fun p=>globalTripleCoproduct a c η hc θ k p x)

theorem globalCoproduct_coassociative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (x : UnitalShuffle a c η hc θ) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id (globalCoproduct a c η hc θ x))=
      TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ) (globalCoproduct a c η hc θ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of k x => exact globalCoproduct_coassociative_lof a c η hc θ hχ k x
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalShuffleCoalgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable instance globalCoalgebra (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)] :
    Coalgebra ℚ (UnitalShuffle a c η hc θ) where
  comul := globalCoproduct a c η hc θ
  counit := globalCounit a c η hc θ
  coassoc := LinearMap.ext (globalCoproduct_coassociative a c η hc θ hχ.out)
  rTensor_counit_comp_comul := LinearMap.ext (globalCoproduct_counit_left a c η hc θ)
  lTensor_counit_comp_comul := LinearMap.ext (globalCoproduct_counit_right a c η hc θ)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic DimensionSplit WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convVanishes_mul {n m : ℕ}
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) (hg : convVanishes a c η hc θ m g) :
    convVanishes a c η hc θ (n+m) (f*g) := by
  intro k hk x
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ A (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)))=0
  rw [globalCoproduct_lof]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro s _
  change LinearMap.mul' ℚ A (TensorProduct.map f.ofConv g.ofConv
    (globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩
      ⟨right s.val,s.property.2⟩ k.2 _))=0
  rw [globalTensorGrade_map_vanishes a c η hc θ n m f g hf hg]
  · exact (LinearMap.mul' ℚ A).map_zero
  · rw [←dimensionSize_add,left_add_right]
    exact hk

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalConvolutionQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convVanishes_zeroMap (n : ℕ) :
    convVanishes a c η hc θ n (0 : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) := by
  intro k hk x
  rfl

lemma convVanishes_add {n : ℕ}
    {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) (hg : convVanishes a c η hc θ n g) :
    convVanishes a c η hc θ n (f+g) := by
  intro k hk x
  change f.ofConv _+g.ofConv _=0
  rw [hf k hk x,hg k hk x,add_zero]

noncomputable def convolutionIdeal (n : ℕ) :
    TwoSidedIdeal (WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :=
  TwoSidedIdeal.mk' {f | convVanishes a c η hc θ n f}
    (convVanishes_zeroMap a c η hc θ n)
    (convVanishes_add a c η hc θ) (convVanishes_neg a c η hc θ)
    (fun {f g} hg=>by
      change convVanishes a c η hc θ n (f*g)
      simpa only [zero_add] using convVanishes_mul a c η hc θ
        (convVanishes_zero a c η hc θ f) hg)
    (fun {f g} hf=>by
      change convVanishes a c η hc θ n (f*g)
      simpa only [add_zero] using convVanishes_mul a c η hc θ hf
        (convVanishes_zero a c η hc θ g))

abbrev ConvolutionQuotient (n : ℕ) := (convolutionIdeal a c η hc θ (A := A) n).ringCon.Quotient

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalWordPairing
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J K : Type*}

noncomputable def functionalWord (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ)
    (l : List K) : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) := (l.map (fun i=>toConv (f i))).prod

end ElementaryPositivity.RawShuffle

end

end OAI
end


