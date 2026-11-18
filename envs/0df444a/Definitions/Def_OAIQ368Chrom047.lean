-- Prove2me | Definitions.Def_OAIQ368Chrom047
-- name    : OAIQ368Chrom047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:19:35.744732+00:00
-- url     : https://prove2.me/theorems/1140afbd-5eb9-481f-a6af-1983ceaa187d
-- title:
--   Definitions bundle OAIQ368Chrom047 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 7 definitions and 38 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.convSeries`, `OAI.ElementaryPositivity.RawShuffle.convolutionJ`, `OAI.ElementaryPositivity.RawShuffle.convolutionProjection`, `OAI.ElementaryPositivity.RawShuffle.globalPrimitiveLog`, `OAI.ElementaryPositivity.RawShuffle.globalPrimitiveProjection`, `OAI.ElementaryPositivity.RawShuffle.primitiveBasisDual`, `OAI.ElementaryPositivity.RawShuffle.primitiveBasisRetraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Shuffle_GlobalConvolutionQuotient`, `Chromatic_Shuffle_GlobalConvolutionSeries`, `Chromatic_Shuffle_GlobalCoproductCocommutative`, `Chromatic_Shuffle_GlobalPBWBasis`, `Chromatic_Shuffle_GlobalPBWIndependent`, `Chromatic_Shuffle_GlobalPrimitiveLog`, `Chromatic_Shuffle_GlobalSeriesEvaluation`, `Chromatic_Shuffle_GlobalShuffleCoalgebra`, `Chromatic_Shuffle_GlobalTensorGradeProduct`, `Chromatic_Shuffle_GradedCoproduct`, `Chromatic_Shuffle_NormalizedTensorSymbol`, `Chromatic_Shuffle_SymbolSwap`, `Chromatic_Shuffle_TensorSymbolSwap`, `Chromatic_Shuffle_UnitalCoproductComparison`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom046` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom049`; the proofs of `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent` and `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom046

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_NormalizedTensorSymbol
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma normalizedTensorSymbol_eq_zero_iff (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (f : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W f=0 ↔
      mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
        (refinedCenterPolynomial a c η hc θ L R hL hR f.val)=0 := by
  change map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
    (internalNumerator a L R)*tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f=0 ↔ _
  rw [SymbolCoordinates.scalar_mul_eq_zero_iff _ (internalNumerator_ne_zero a L R)]
  rw [←denominator_tensorClearedLeading a c η hc θ L R hL hR hχL hχR W f,
    SymbolCoordinates.scalar_mul_eq_zero_iff _ (internalDenominator_ne_zero a L R)]

theorem normalizedTensorSymbol_detect (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ) (x : sourceTensorFiltration a c η hc θ d e W)
    (h : ∀ (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
      (hd : L.dim=d) (he : R.dim=e),
      normalizedTensorSymbol a c η hc θ L R hL hR
        (pairSymmetric_of_slope a c η θ hχ L hL) (pairSymmetric_of_slope a c η θ hχ R hR) W
        (hd ▸ he ▸ x)=0) :
    x.val∈sourceTensorFiltration a c η hc θ d e (W+1) := by
  apply tensor_leading_restrictions_detect a c η hc θ d e W x.val x.property
  rintro ⟨L,hoL,hL,hd,k,z⟩ ⟨R,hoR,hR,he,l,w⟩ hw
  subst d
  subst e
  have hp:=(normalizedTensorSymbol_eq_zero_iff a c η hc θ L R hL hR _ _ W x).mp (h L R hL hR rfl rfl)
  have ht:=congrArg (fun p=>componentTensor a (SlopeArithmetic.slope c η) (.node L R) (k,l)
    (MvPolynomial.coeff (z.sumElim w) p)) hp
  have heq : 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W := by
    change (2*L.totalDegree k+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W at hw
    omega
  rw [coeff_mapLinear,componentTensor_weightComponent,ite_eq_left heq,
    MvPolynomial.coeff_zero,map_zero,
    refinedCenterPolynomial_coeff_test] at ht
  exact ht

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GradedCoproduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SplitTree

lemma normalizedTensorSymbol_next_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (x : sourceTensorFiltration a c η hc θ L.dim R.dim W)
    (hx : x.val∈sourceTensorFiltration a c η hc θ L.dim R.dim (W+1)) :
    normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W x=0 := by
  rw [normalizedTensorSymbol_eq_zero_iff]
  ext s
  rw [coeff_mapLinear,MvPolynomial.coeff_zero]
  apply componentTensor_detect a (SlopeArithmetic.slope c η) (.node L R)
  rintro ⟨k,l⟩
  rw [componentTensor_weightComponent]
  split_ifs with hw
  · let z := s.comapDomain Sum.inl Sum.inl_injective.injOn
    let w := s.comapDomain Sum.inr Sum.inr_injective.injOn
    have hsw : z.sumElim w=s := Finsupp.comapDomain_sumElim_comapDomain s
    rw [←hsw,refinedCenterPolynomial_coeff_test]
    apply tensorTest_next_zero a c η hc θ L R hL hR W x.val hx k l z w
    change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W at hw
    omega
  · rfl
end SplitTree

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
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
lemma centerPower_swap (a : I → I → ℕ) (L R : SplitTree I) (φ : ℤ → ℕ)
    (hs : ∀ z t,eulerForm a (L.leafDimension z) (R.leafDimension t)=
      eulerForm a (R.leafDimension t) (L.leafDimension z)) :
    rename (Equiv.sumComm L.Centers R.Centers) (centerPower a (L.node R) φ)=
      C (crossSign a L R φ)*centerPower a (R.node L) φ := by
  rw [centerPower_node,centerPower_node,map_mul,map_mul,crossPower_swap a L R φ hs]
  simp only [rename_rename,Equiv.sumComm_apply,Function.comp_def,Sum.swap_inl,Sum.swap_inr]
  ring

namespace Regroup
lemma clearedLeading_swap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : sourceFiltration a c η hc θ (L.node R).dim W) :
    clearedLeading a c η hc θ (.node R L) ⟨hR,hL⟩
        (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W
        (filtrationDimensionEquiv a c η hc θ (Regroup.swap L R).dimension W f)=
      crossSign a L R (fun e=>(-e).toNat) •
        extendPolynomial ((Regroup.swap L R).equivalence
          (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
          (Regroup.swap L R).centers
          (clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩
            (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f) := by
  have hs (z : L.Centers) (t : R.Centers) :
      eulerForm a (L.leafDimension z) (R.leafDimension t)=
        eulerForm a (R.leafDimension t) (L.leafDimension z) := by
    obtain ⟨hz,hzs⟩:=L.leafDimension_onSlope c η θ hL z
    obtain ⟨ht,hts⟩:=R.leafDimension_onSlope c η θ hR t
    exact hχ _ _ hz ht hzs hts
  have hd : rename (Regroup.swap L R).centers
      (centerDenominator a (L.node R) (L.node R).centerPairs)=
      C (crossSign a L R (fun e=>(-e).toNat))*
        centerDenominator a (R.node L) (R.node L).centerPairs :=
    centerPower_swap a L R (fun e=>(-e).toNat) hs
  apply scalar_mul_injective _ (centerDenominator_ne_zero a (R.node L))
  dsimp only
  rw [denominator_clearedLeading a c η hc θ (R.node L) ⟨hR,hL⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W,
    filtrationDimensionEquiv_val,
    totalLeadingPolynomial_natural a c η hc θ (Regroup.swap L R) ⟨hL,hR⟩ ⟨hR,hL⟩ W,
    ←denominator_clearedLeading a c η hc θ (L.node R) ⟨hL,hR⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f,
    map_mul,extendPolynomial_map_algebra,hd,map_mul,map_C]
  rw [Algebra.smul_def]
  simp only [MvPolynomial.algebraMap_apply]
  ring

lemma normalizedSymbol_swap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (f : sourceFiltration a c η hc θ (L.node R).dim W) :
    normalizedSymbol a c η hc θ (.node R L) ⟨hR,hL⟩
        (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W
        (filtrationDimensionEquiv a c η hc θ (Regroup.swap L R).dimension W f)=
      (-1:ℚ)^eulerForm a L.dim R.dim •
        extendPolynomial ((Regroup.swap L R).equivalence
          (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
          (Regroup.swap L R).centers
          (normalizedSymbol a c η hc θ (.node L R) ⟨hL,hR⟩
            (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f) := by
  have hs (z : L.Centers) (t : R.Centers) :
      eulerForm a (L.leafDimension z) (R.leafDimension t)=
        eulerForm a (R.leafDimension t) (L.leafDimension z) := by
    obtain ⟨hz,hzs⟩:=L.leafDimension_onSlope c η θ hL z
    obtain ⟨ht,hts⟩:=R.leafDimension_onSlope c η θ hR t
    exact hχ _ _ hz ht hzs hts
  have hn : rename (Regroup.swap L R).centers
      (centerNumerator a (L.node R) (L.node R).centerPairs)=
      C (crossSign a L R Int.toNat)*centerNumerator a (R.node L) (R.node L).centerPairs :=
    centerPower_swap a L R Int.toNat hs
  have hsign : (-1:ℚ)^eulerForm a L.dim R.dim*crossSign a L R Int.toNat=
      crossSign a L R (fun e=>(-e).toNat) := by
    rw [←crossSign_pos_neg]
    calc
      _ = (crossSign a L R Int.toNat*crossSign a L R Int.toNat)*
        crossSign a L R (fun e=>(-e).toNat) := by ring
      _ = _ := by rw [crossSign_sq,one_mul]
  change map _ (centerNumerator a (R.node L) (R.node L).centerPairs)*
    clearedLeading a c η hc θ (.node R L) ⟨hR,hL⟩
      (pairSymmetric_of_slope a c η θ hχ _ ⟨hR,hL⟩) W _ =
    (-1:ℚ)^eulerForm a L.dim R.dim •
    extendPolynomial _ _ (map _ (centerNumerator a (L.node R) (L.node R).centerPairs)*
      clearedLeading a c η hc θ (.node L R) ⟨hL,hR⟩
        (pairSymmetric_of_slope a c η θ hχ _ ⟨hL,hR⟩) W f)
  rw [clearedLeading_swap a c η hc θ hχ L R hL hR W f,
    map_mul,extendPolynomial_map_algebra,hn,map_mul,map_C]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_apply]
  have hh:=congrArg (fun r : ℚ =>
    (C ((algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node R L))) r) :
      MvPolynomial (R.node L).Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node R L)))) hsign
  simp only [map_mul] at hh
  rw [←hh]
  ring

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorSymbolSwap
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
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

lemma normalizedTensorSymbol_swap (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (hχL : L.PairSymmetric a) (hχR : R.PairSymmetric a) (W : ℤ)
    (z : sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    normalizedTensorSymbol a c η hc θ R L hR hL hχR hχL W
      (sourceTensorComm a c η hc θ L.dim R.dim W z)=
    extendPolynomial ((Regroup.swap L R).equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
      (Regroup.swap L R).centers
      (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W z) := by
  let f := (normalizedTensorSymbol a c η hc θ R L hR hL hχR hχL W).comp
    (sourceTensorComm a c η hc θ L.dim R.dim W).toLinearMap
  let g := (extendPolynomial
    ((Regroup.swap L R).equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
    (Regroup.swap L R).centers).toLinearMap.comp
    (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W)
  have he : f=g := by
    apply linearMap_span_ext
    rintro _ ⟨u,v,x,y,huv,hx,hy,rfl⟩
    change normalizedTensorSymbol a c η hc θ R L hR hL hχR hχL W
      (sourceTensorComm a c η hc θ L.dim R.dim W ⟨x⊗ₜ[ℚ]y,_⟩)=
      extendPolynomial _ _ (normalizedTensorSymbol a c η hc θ L R hL hR hχL hχR W ⟨x⊗ₜ[ℚ]y,_⟩)
    by_cases hw : W=u+v
    · subst W
      have hl:=normalizedTensorSymbol_tmul_eq a c η hc θ R L hR hL hχR hχL (u+v) v u
        (by omega) ⟨y,hy⟩ ⟨x,hx⟩
      rw [normalizedTensorSymbol_tmul a c η hc θ L R hL hR hχL hχR u v ⟨x,hx⟩ ⟨y,hy⟩]
      exact hl.trans (box_swap _ _).symm
    · have hnext : x⊗ₜ[ℚ]y∈sourceTensorFiltration a c η hc θ L.dim R.dim (W+1) :=
        Submodule.subset_span ⟨u,v,x,y,by omega,hx,hy,rfl⟩
      rw [normalizedTensorSymbol_next_zero a c η hc θ L R hL hR hχL hχR W _ hnext,map_zero]
      apply normalizedTensorSymbol_next_zero
      exact comm_mem_tensorFiltration _ _ (W+1) _ hnext
  exact LinearMap.congr_fun he z

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
open LinearFiltration
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cocommTensorBAlgebra
theorem separationCoproduct_cocommutative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ (d+e) W) :
    separationCoproduct a c η hc θ e d hs.symm W
      (sourceGradeDimensionEquiv a c η hc θ (add_comm d e) W f)=
      (-1:ℚ)^eulerForm a d e • sourceTensorGradeComm a c η hc θ d e W
        (separationCoproduct a c η hc θ d e hs W f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [sourceGradeDimensionEquiv_mk a c η hc θ (add_comm d e) W f,
      separationCoproduct_mk a c η hc θ e d hs.symm W,
      separationCoproduct_mk a c η hc θ d e hs W,
      sourceTensorGradeComm_mk a c η hc θ d e W]
    apply sub_eq_zero.mp
    change Submodule.Quotient.mk
      (separationCoefficientRestricted a c η hc θ e d hs.symm W 0
        (filtrationDimensionEquiv a c η hc θ (add_comm d e) W f) -
        (-1:ℚ)^eulerForm a d e •
          SplitTree.sourceTensorComm a c η hc θ d e W
            (separationCoefficientRestricted a c η hc θ d e hs W 0 f))=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    let x := separationCoefficientRestricted a c η hc θ e d hs.symm W 0
        (filtrationDimensionEquiv a c η hc θ (add_comm d e) W f) -
      (-1:ℚ)^eulerForm a d e • SplitTree.sourceTensorComm a c η hc θ d e W
        (separationCoefficientRestricted a c η hc θ d e hs W 0 f)
    change x.val ∈ sourceTensorFiltration a c η hc θ e d (W+1)
    apply SplitTree.normalizedTensorSymbol_detect a c η hc θ hχ e d W x
    intro R L hR hL he hd
    subst d
    subst e
    let N := SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL
      (SplitTree.pairSymmetric_of_slope a c η θ hχ R hR)
      (SplitTree.pairSymmetric_of_slope a c η θ hχ L hL) W
    let C := separationCoefficientRestricted a c η hc θ L.dim R.dim hs W 0 f
    let C' := separationCoefficientRestricted a c η hc θ R.dim L.dim hs.symm W 0
      (filtrationDimensionEquiv a c η hc θ (add_comm L.dim R.dim) W f)
    change N (C' - (-1:ℚ)^eulerForm a L.dim R.dim •
      SplitTree.sourceTensorComm a c η hc θ L.dim R.dim W C)=0
    rw [N.map_sub, N.map_smul]
    change SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL _ _ W C' -
      (-1:ℚ)^eulerForm a L.dim R.dim •
        SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL _ _ W
          (SplitTree.sourceTensorComm a c η hc θ L.dim R.dim W C)=0
    have hC := SplitTree.coproduct_normalized_symbol a c η hc θ hχ L R hL hR W f
    have hC' := SplitTree.coproduct_normalized_symbol a c η hc θ hχ R L hR hL W
      (filtrationDimensionEquiv a c η hc θ (add_comm L.dim R.dim) W f)
    change SplitTree.normalizedTensorSymbol a c η hc θ L R hL hR _ _ W C=_ at hC
    change SplitTree.normalizedTensorSymbol a c η hc θ R L hR hL _ _ W C'=_ at hC'
    rw [hC',SplitTree.normalizedTensorSymbol_swap,hC,
      SplitTree.Regroup.normalizedSymbol_swap a c η hc θ hχ L R hL hR]
    exact sub_self _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cocommTensorBCommRing cocommTensorBAlgebra

lemma separationCoproduct_cocommutative_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : slope c η d=slope c η e) (W : ℤ)
    (x : B a (slope c η) (d+e)) (hx : x∈sourceFiltration a c η hc θ (d+e) W) :
    separationCoefficient a c η hc (d:=e) (e:=d) hs.symm 0
        (castB a (slope c η) (add_comm d e) x) -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (separationCoefficient a c η hc (d:=d) (e:=e) hs 0 x) ∈
      sourceTensorFiltration a c η hc θ e d (W+1) := by
  have h := separationCoproduct_cocommutative a c η hc θ hχ d e hs W
    (Submodule.Quotient.mk ⟨x,hx⟩)
  rw [sourceGradeDimensionEquiv_mk,separationCoproduct_mk,separationCoproduct_mk,
    sourceTensorGradeComm_mk] at h
  have hz := sub_eq_zero.mpr h
  change Submodule.Quotient.mk
    (separationCoefficientRestricted a c η hc θ e d hs.symm W 0
        (filtrationDimensionEquiv a c η hc θ (add_comm d e) W ⟨x,hx⟩) -
      (-1:ℚ)^eulerForm a d e • SplitTree.sourceTensorComm a c η hc θ d e W
        (separationCoefficientRestricted a c η hc θ d e hs W 0 ⟨x,hx⟩))=0 at hz
  have hm := (Submodule.Quotient.mk_eq_zero
    (next (sourceTensorFiltration a c η hc θ e d W)
      (sourceTensorFiltration a c η hc θ e d (W+1)))).mp hz
  change separationCoefficient a c η hc hs.symm 0
      (filtrationDimensionEquiv a c η hc θ (add_comm d e) W ⟨x,hx⟩).val -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (separationCoefficient a c η hc hs 0 x)∈sourceTensorFiltration a c η hc θ e d (W+1) at hm
  rw [filtrationDimensionEquiv_castB] at hm
  exact hm

lemma unitalSeparationConstant_cocommutative_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (W : ℤ)
    (x : B a (slope c η) (d+e)) (hx : x∈unitalSourceFiltration a c η hc θ (d+e) W) :
    unitalSeparationConstant a c η hc e d (he.compatible hd)
        (castB a (slope c η) (add_comm d e) x) -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (unitalSeparationConstant a c η hc d e (hd.compatible he) x) ∈
      unitalSourceTensorFiltration a c η hc θ e d (W+1) := by
  by_cases hd0 : d=0
  · subst d
    have hL := unitalSeparationConstant_zero_left a c η hc e
      (castB a (slope c η) (zero_add e) x)
    have hR := unitalSeparationConstant_zero_right a c η hc e
      (castB a (slope c η) (zero_add e) x)
    simp only [castB_trans,castB_rfl] at hL hR
    rw [hL,hR,TensorProduct.comm_tmul]
    simp [eulerForm]
  by_cases he0 : e=0
  · subst e
    have hL := unitalSeparationConstant_zero_left a c η hc d
      (castB a (slope c η) (add_zero d) x)
    have hR := unitalSeparationConstant_zero_right a c η hc d
      (castB a (slope c η) (add_zero d) x)
    simp only [castB_rfl] at hL hR
    rw [hL,hR,TensorProduct.comm_tmul]
    simp [eulerForm]
  have hde : slope c η d=slope c η e := (hd.compatible he).resolve_left hd0 |>.resolve_left he0
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) (add_ne_zero_left _ _ hd0) W] at hx
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ e d he0 hd0,
    unitalSeparationConstant_eq a c η hc e d _ hde.symm,
    unitalSeparationConstant_eq a c η hc d e _ hde]
  exact separationCoproduct_cocommutative_filtration a c η hc θ hχ d e hde W x hx

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma unitalGradeCoproduct_cocommutative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) (W : ℤ)
    (x : UnitalSourceGrade a c η hc θ (d+e) W) :
    unitalGradeCoproduct a c η hc θ e d (he.compatible hd) W
        (unitalGradeCast a c η hc θ (add_comm d e) rfl x)=
      (-1:ℚ)^eulerForm a d e • unitalTensorGradeComm a c η hc θ d e W
        (unitalGradeCoproduct a c η hc θ d e (hd.compatible he) W x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    let : AddCommGroup (LinearDetection.additiveTensorFiltration
        (unitalSourceFiltration a c η hc θ e) (unitalSourceFiltration a c η hc θ d) W) :=
      Submodule.addCommGroup _
    let : Module ℚ (LinearDetection.additiveTensorFiltration
        (unitalSourceFiltration a c η hc θ e) (unitalSourceFiltration a c η hc θ d) W) :=
      Submodule.module _
    rw [unitalGradeCast_mk,unitalGradeCoproduct_mk,unitalGradeCoproduct_mk]
    apply sub_eq_zero.mp
    unfold unitalSourceTensorFiltration at *
    change Submodule.Quotient.mk
      ((⟨unitalSeparationConstant a c η hc e d (he.compatible hd)
          (unitalFiltrationCast a c η hc θ (add_comm d e) rfl x).val, _⟩ :
          LinearDetection.additiveTensorFiltration (unitalSourceFiltration a c η hc θ e)
            (unitalSourceFiltration a c η hc θ d) W) -
        (-1:ℚ)^eulerForm a d e • (tensorFiltrationComm
          (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e) W
          ⟨unitalSeparationConstant a c η hc d e (hd.compatible he) x.val, _⟩ :
            LinearDetection.additiveTensorFiltration (unitalSourceFiltration a c η hc θ e)
            (unitalSourceFiltration a c η hc θ d) W))=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change unitalSeparationConstant a c η hc e d (he.compatible hd)
      (unitalFiltrationCast a c η hc θ (add_comm d e) rfl x).val -
      (-1:ℚ)^eulerForm a d e • TensorProduct.comm ℚ _ _
        (unitalSeparationConstant a c η hc d e (hd.compatible he) x.val)∈
          unitalSourceTensorFiltration a c η hc θ e d (W+1)
    rw [unitalFiltrationCast_val]
    exact unitalSeparationConstant_cocommutative_filtration a c η hc θ hχ d e hd he W x.val x.property

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCocommutative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.RawShuffle.globalCoalgebra _root_.OAI.ElementaryPositivity.RawShuffle.instAlgebraRatSignedGlobalTensor _root_.OAI.ElementaryPositivity.RawShuffle.instRingSignedGlobalTensorOfFactSlopeEulerSymmetric _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

lemma globalPairCoproduct_swap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : slopeDimensions c η hc θ) {t : I → ℕ} (h : d.val+e.val=t)
    (W : ℤ) (x : UnitalSourceGrade a c η hc θ t W) :
    globalTensorGradeInclusion a c η hc θ e d W
      (unitalGradeCoproduct a c η hc θ e.val d.val (e.property.compatible d.property) W
        (unitalGradeCast a c η hc θ ((add_comm _ _).trans h).symm rfl x))=
      globalSignedComm a c η hc θ
        (globalTensorGradeInclusion a c η hc θ d e W
          (unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) W
            (unitalGradeCast a c η hc θ h.symm rfl x))) := by
  have hC := unitalGradeCoproduct_cocommutative a c η hc θ hχ d.val e.val
    d.property e.property W (unitalGradeCast a c η hc θ h.symm rfl x)
  rw [unitalGradeCast_trans] at hC
  rw [hC,map_smul,globalTensorGradeInclusion_comm]
  rw [globalSignedComm,LinearMap.comp_apply,globalSignOperator_inclusion,map_smul]
  rfl

lemma globalSplitCoproduct_swap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (s : SlopeSplit c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k (slopeSplitSwap c η hc θ k.1.val s) x=
      globalSignedComm a c η hc θ (globalSplitCoproduct a c η hc θ k s x) := by
  rw [globalSplitCoproduct_dimensions a c η hc θ k
    (slopeSplitSwap c η hc θ k.1.val s) (right s.val) (left s.val)
    (left_swap s.val) (right_swap s.val) s.property.2 s.property.1
    ((add_comm _ _).trans (left_add_right s.val)) x]
  rw [globalSplitCoproduct_dimensions a c η hc θ k s (left s.val) (right s.val)
    rfl rfl s.property.1 s.property.2 (left_add_right s.val) x]
  exact globalPairCoproduct_swap a c η hc θ hχ
    ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ (left_add_right s.val) k.2 x

theorem globalCoproduct_cocommutative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (x : UnitalShuffle a c η hc θ) :
    globalSignedComm a c η hc θ (globalCoproduct a c η hc θ x)=
      globalCoproduct a c η hc θ x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of k x =>
    change globalSignedComm a c η hc θ
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
        globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)
    rw [globalCoproduct_lof]
    simp only [map_sum]
    calc
      _=∑ s : SlopeSplit c η hc θ k.1.val,
        globalSplitCoproduct a c η hc θ k (slopeSplitSwap c η hc θ k.1.val s) x :=
          Finset.sum_congr rfl (fun s _=>(globalSplitCoproduct_swap a c η hc θ hχ k s x).symm)
      _=_ := Equiv.sum_comp (slopeSplitSwap c η hc θ k.1.val)
        (fun s : SlopeSplit c η hc θ k.1.val => globalSplitCoproduct a c η hc θ k s x)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalShuffleCoalgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic DimensionSplit WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

lemma convVanishes_pow {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (n : ℕ) :
    convVanishes a c η hc θ n (f^n) := by
  induction n with
  | zero => exact convVanishes_zero a c η hc θ _
  | succ n ih =>
    rw [pow_succ]
    exact convVanishes_mul a c η hc θ ih hf

noncomputable def convolutionJ : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ) :=
  toConv LinearMap.id - 1

lemma convolutionJ_vanishes : convVanishes a c η hc θ 1 (convolutionJ a c η hc θ) := by
  intro k hk x
  have hd : k.1.val=0 := (dimensionSize_eq_zero _).mp (by omega)
  change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x -
    algebraMap ℚ (UnitalShuffle a c η hc θ)
      (globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=0
  rw [Algebra.algebraMap_eq_smul_one,sub_eq_zero]
  change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x =
    globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) •
      globalUnit a c η hc θ
  exact zeroDimension_lof_scalar a c η hc θ k hd x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalConvolutionQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def convolutionProjection (n : ℕ) :
    WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A) →ₐ[ℚ] ConvolutionQuotient a c η hc θ (A := A) n :=
  (convolutionIdeal a c η hc θ n).ringCon.mkₐ ℚ

lemma convolutionProjection_eq_zero_iff (n : ℕ)
    (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :
    convolutionProjection a c η hc θ n f=0 ↔ convVanishes a c η hc θ n f := by
  have h := (convolutionIdeal a c η hc θ (A := A) n).ringCon.eq (a := f) (b := 0)
  change convolutionProjection a c η hc θ n f=0 ↔ _ at h
  apply h.trans
  rw [←TwoSidedIdeal.mem_iff]
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f

lemma convolutionProjection_eq_iff (n : ℕ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :
    convolutionProjection a c η hc θ n f=convolutionProjection a c η hc θ n g ↔
      ∀ k : SlopeWeight c η hc θ, dimensionSize k.1.val < n →
        ∀ x : unitalComponent a c η hc θ k,
          f.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
            g.ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) := by
  rw [←sub_eq_zero,←map_sub,convolutionProjection_eq_zero_iff]
  simp only [convVanishes,WithConv.ofConv_sub,LinearMap.sub_apply,sub_eq_zero]

lemma convolutionProjection_nilpotent (n : ℕ)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) :
    (convolutionProjection a c η hc θ n f)^n=0 := by
  rw [←map_pow,convolutionProjection_eq_zero_iff]
  exact convVanishes_pow a c η hc θ hf n

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalConvolutionSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def convSeries (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (p : PowerSeries ℚ) : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A) :=
  toConv (DirectSum.toModule ℚ _ _ (fun k=>∑ r ∈ Finset.range (dimensionSize k.1.val+1),
    PowerSeries.coeff r p • (f^r).ofConv.comp (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)))

lemma convSeries_lof (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (p : PowerSeries ℚ) (k : SlopeWeight c η hc θ) (x : unitalComponent a c η hc θ k) :
    (convSeries a c η hc θ f p).ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      ∑ r ∈ Finset.range (dimensionSize k.1.val+1), PowerSeries.coeff r p •
        (f^r).ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) := by
  rw [convSeries,ofConv_toConv,DirectSum.toModule_lof]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]

lemma convolutionProjection_series (n : ℕ)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (p : PowerSeries ℚ) :
    convolutionProjection a c η hc θ n (convSeries a c η hc θ f p)=
      nilEval (convolutionProjection a c η hc θ n f) p := by
  rw [nilEval_eq_sum (convolutionProjection_nilpotent a c η hc θ n hf)]
  simp only [←map_pow,←map_smul,←map_sum]
  rw [convolutionProjection_eq_iff]
  intro k hk x
  rw [convSeries_lof]
  simp only [ofConv_sum,ofConv_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro r hr hsmall
  rw [Finset.mem_range,not_lt] at hsmall
  rw [convVanishes_pow a c η hc θ hf r k (by omega) x,smul_zero]

lemma convolutionProjection_jointly_injective
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (h : ∀ n, convolutionProjection a c η hc θ n f=convolutionProjection a c η hc θ n g) : f=g := by
  apply ofConv_injective
  apply DirectSum.linearMap_ext
  intro k
  ext x
  exact (convolutionProjection_eq_iff a c η hc θ (dimensionSize k.1.val+1) f g).mp
    (h _) k (by omega) x

lemma convSeries_post (φ : A →ₐ[ℚ] B)
    (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) (p : PowerSeries ℚ) :
    convPost φ (convSeries a c η hc θ f p)=convSeries a c η hc θ (convPost φ f) p := by
  apply ofConv_injective
  apply DirectSum.linearMap_ext
  intro k
  ext x
  simp only [LinearMap.comp_apply]
  rw [convPost_apply,convSeries_lof,convSeries_lof]
  simp only [map_sum,map_smul,←map_pow,convPost_apply]

lemma convVanishes_one_add_product {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (hg : convVanishes a c η hc θ 1 g) :
    convVanishes a c η hc θ 1 ((1+f)*(1+g)-1) := by
  rw [show (1+f)*(1+g)-1=f+g+f*g by noncomm_ring]
  exact convVanishes_add a c η hc θ (convVanishes_add a c η hc θ hf hg)
    (convVanishes_mono a c η hc θ (by omega : 1 ≤ 1+1) (convVanishes_mul a c η hc θ hf hg))

lemma convSeries_log_product {f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hfg : Commute f g) (hf : convVanishes a c η hc θ 1 f) (hg : convVanishes a c η hc θ 1 g) :
    convSeries a c η hc θ ((1+f)*(1+g)-1) (PowerSeries.log ℚ)=
      convSeries a c η hc θ f (PowerSeries.log ℚ)+convSeries a c η hc θ g (PowerSeries.log ℚ) := by
  apply convolutionProjection_jointly_injective a c η hc θ
  intro n
  rw [convolutionProjection_series a c η hc θ n (convVanishes_one_add_product a c η hc θ hf hg),
    map_add,convolutionProjection_series a c η hc θ n hf,
    convolutionProjection_series a c η hc θ n hg]
  simp only [map_sub,map_mul,map_add,map_one]
  exact nilEval_log_mul_of_commute (hfg.map (convolutionProjection a c η hc θ n))
    ⟨n,convolutionProjection_nilpotent a c η hc θ n hf⟩
    ⟨n,convolutionProjection_nilpotent a c η hc θ n hg⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveLog
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv ElementaryPositivity.FiniteLog
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

lemma signedLeftRight_convolution :
    toConv (signedLeft a c η hc θ) * toConv (signedRight a c η hc θ)=
      toConv (globalCoproductAlgHom a c η hc θ).toLinearMap := by
  apply ofConv_injective
  apply LinearMap.ext
  intro x
  rw [LinearMap.convMul_apply]
  exact signedLeftRight_product a c η hc θ (globalCoproduct a c η hc θ x)

lemma signedRightLeft_convolution :
    toConv (signedRight a c η hc θ) * toConv (signedLeft a c η hc θ)=
      toConv (globalCoproductAlgHom a c η hc θ).toLinearMap := by
  apply ofConv_injective
  apply LinearMap.ext
  intro x
  rw [LinearMap.convMul_apply]
  exact (signedRightLeft_product a c η hc θ (globalCoproduct a c η hc θ x)).trans
    (globalCoproduct_cocommutative a c η hc θ hχ.out x)

lemma convPost_id {A : Type*} [Ring A] [Algebra ℚ A]
    (φ : UnitalShuffle a c η hc θ →ₐ[ℚ] A) :
    convPost φ (toConv LinearMap.id)=toConv φ.toLinearMap := rfl

lemma convPost_J {A : Type*} [Ring A] [Algebra ℚ A]
    (φ : UnitalShuffle a c η hc θ →ₐ[ℚ] A) :
    convPost φ (convolutionJ a c η hc θ)=toConv φ.toLinearMap-1 := by
  rw [convolutionJ,map_sub,convPost_id,map_one]

lemma convVanishes_post {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) {n : ℕ} {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) : convVanishes a c η hc θ n (convPost φ f) := by
  intro k hk x
  rw [convPost_apply,hf k hk x,map_zero]

lemma signedConvolution_J_product :
    (1+convPost (signedLeftAlgHom a c η hc θ) (convolutionJ a c η hc θ))*
      (1+convPost (signedRightAlgHom a c η hc θ) (convolutionJ a c η hc θ))-1=
      convPost (globalCoproductAlgHom a c η hc θ) (convolutionJ a c η hc θ) := by
  simp only [convPost_J]
  have h (z : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] SignedGlobalTensor a c η hc θ)) : 1+(z-1)=z := by abel
  rw [h,h]
  exact congrArg (fun x=>x-1) (signedLeftRight_convolution a c η hc θ)

lemma signedConvolution_J_commute :
    Commute (convPost (signedLeftAlgHom a c η hc θ) (convolutionJ a c η hc θ))
      (convPost (signedRightAlgHom a c η hc θ) (convolutionJ a c η hc θ)) := by
  have h : Commute (toConv (signedLeft a c η hc θ)) (toConv (signedRight a c η hc θ)) :=
    (signedLeftRight_convolution a c η hc θ).trans (signedRightLeft_convolution a c η hc θ).symm
  simp only [convPost_J]
  exact (h.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)

noncomputable def globalPrimitiveLog : UnitalShuffle a c η hc θ →ₗ[ℚ] UnitalShuffle a c η hc θ :=
  (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv

theorem globalPrimitiveLog_primitive (x : UnitalShuffle a c η hc θ) :
    globalCoproduct a c η hc θ (globalPrimitiveLog a c η hc θ x)=
      globalPrimitiveLog a c η hc θ x⊗ₜ[ℚ]globalUnit a c η hc θ+
        globalUnit a c η hc θ⊗ₜ[ℚ]globalPrimitiveLog a c η hc θ x := by
  have h := convSeries_log_product a c η hc θ (signedConvolution_J_commute a c η hc θ)
    (convVanishes_post a c η hc θ (signedLeftAlgHom a c η hc θ)
      (convolutionJ_vanishes a c η hc θ))
    (convVanishes_post a c η hc θ (signedRightAlgHom a c η hc θ)
      (convolutionJ_vanishes a c η hc θ))
  rw [signedConvolution_J_product,←convSeries_post,←convSeries_post,←convSeries_post] at h
  exact congrArg (fun f=>f.ofConv x) h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalSeriesEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma convSeries_eventually_finite
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f) (p : PowerSeries ℚ)
    (x : UnitalShuffle a c η hc θ) :
    ∃ N : ℕ, ∀ n, N ≤ n → (convSeries a c η hc θ f p).ofConv x=
      ∑ r ∈ Finset.range n,PowerSeries.coeff r p • (f^r).ofConv x := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0,fun n _=>by simp⟩
  | add x y hx hy =>
    obtain ⟨N,hN⟩ := hx
    obtain ⟨M,hM⟩ := hy
    refine ⟨max N M,fun n hn=>?_⟩
    rw [map_add,hN n (le_trans (le_max_left _ _) hn),hM n (le_trans (le_max_right _ _) hn)]
    simp only [map_add,smul_add,Finset.sum_add_distrib]
  | of k x =>
    refine ⟨dimensionSize k.1.val+1,fun n hn=>?_⟩
    change (convSeries a c η hc θ f p).ofConv
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      ∑ r ∈ Finset.range n,PowerSeries.coeff r p •
        (f^r).ofConv (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)
    rw [convSeries_lof]
    apply Finset.sum_subset (Finset.range_mono hn)
    intro r hr hsmall
    rw [Finset.mem_range,not_lt] at hsmall
    rw [convVanishes_pow a c η hc θ hf r k (by omega) x,smul_zero]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma convolution_mul_primitive {A : Type*} [Ring A] [Algebra ℚ A]
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    {x : UnitalShuffle a c η hc θ} (hx : x ∈ globalPrimitives a c η hc θ) :
    (f*g).ofConv x=f.ofConv x*g.ofConv (globalUnit a c η hc θ)+
      f.ofConv (globalUnit a c η hc θ)*g.ofConv x := by
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ A (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ x))=_
  rw [(mem_globalPrimitives a c η hc θ x).mp hx,map_add,map_add]
  simp only [TensorProduct.map_tmul,LinearMap.mul'_apply]

lemma convolution_pow_primitive {A : Type*} [Ring A] [Algebra ℚ A]
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ 1 f)
    {x : UnitalShuffle a c η hc θ} (hx : x ∈ globalPrimitives a c η hc θ)
    (r : ℕ) (hr : 2 ≤ r) : (f^r).ofConv x=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2+r=(1+r)+1 by omega,pow_succ,convolution_mul_primitive a c η hc θ _ _ hx,
    convVanishes_unit a c η hc θ hf]
  have hp := convVanishes_mono a c η hc θ (by omega : 1 ≤ 1+r)
    (convVanishes_pow a c η hc θ hf (1+r))
  rw [convVanishes_unit a c η hc θ hp,mul_zero,zero_mul,add_zero]

lemma convolutionJ_primitive {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) :
    (convolutionJ a c η hc θ).ofConv x=x := by
  change x-algebraMap ℚ (UnitalShuffle a c η hc θ) (globalCounit a c η hc θ x)=x
  rw [globalPrimitive_counit a c η hc θ hx,map_zero,sub_zero]

theorem globalPrimitiveLog_on_primitive {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) : globalPrimitiveLog a c η hc θ x=x := by
  obtain ⟨N,hN⟩ := convSeries_eventually_finite a c η hc θ
    (convolutionJ_vanishes a c η hc θ) (PowerSeries.log ℚ) x
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv x=x
  rw [hN (max N 2) (le_max_left _ _),Finset.sum_eq_single 1]
  · rw [pow_one,convolutionJ_primitive a c η hc θ hx]
    simp
  · intro r hr hr1
    by_cases hr0 : r=0
    · subst r; simp
    · rw [convolution_pow_primitive a c η hc θ (convolutionJ_vanishes a c η hc θ) hx r
        (by omega),smul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (lt_of_lt_of_le (by omega) (le_max_right _ _))))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWIndependent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
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

noncomputable def globalPrimitiveProjection : UnitalShuffle a c η hc θ →ₗ[ℚ] globalPrimitives a c η hc θ :=
  (globalPrimitiveLog a c η hc θ).codRestrict (globalPrimitives a c η hc θ)
    (fun x=>(mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ x))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable Classical.decEq
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
  (w : J → SlopeWeight c η hc θ)
  (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
  (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
  (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
  (hli : LinearIndependent ℚ b)

noncomputable def primitiveBasisRetraction :
    UnitalShuffle a c η hc θ →ₗ[ℚ] Submodule.span ℚ (Set.range b) :=
  (globalPrimitiveLog a c η hc θ).codRestrict _ (fun x=>by
    rw [hspan]
    exact (mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ x))

noncomputable def primitiveBasisDual (j : J) : UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ :=
  (Module.Basis.span hli).coord j ∘ₗ primitiveBasisRetraction a c η hc θ b hspan

end ElementaryPositivity.RawShuffle

end

end OAI
end


