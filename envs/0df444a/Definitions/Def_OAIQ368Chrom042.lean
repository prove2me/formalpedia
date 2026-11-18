-- Prove2me | Definitions.Def_OAIQ368Chrom042
-- name    : OAIQ368Chrom042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:11:13.367004+00:00
-- url     : https://prove2.me/theorems/b2d6b7e3-8520-4720-99dd-99cb383e1e8a
-- title:
--   Definitions bundle OAIQ368Chrom042 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 4 definitions and 16 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SplitTree.clearedLeading`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.clearedLeadingMap`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.normalizedSymbol`, `OAI.ElementaryPositivity.RawShuffle.globalCoproductAlgHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalCoproductUnits`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalCoproductUnits.lean), [`Chromatic_Shuffle_GlobalSeriesEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalSeriesEvaluation.lean), [`Chromatic_Shuffle_GlobalShuffleCoalgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalShuffleCoalgebra.lean), [`Chromatic_Shuffle_PointEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PointEvaluation.lean), [`Chromatic_Shuffle_UnitalCoproductUnits`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalCoproductUnits.lean), [`Chromatic_Walls_UnitalCoproductNaturality`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/UnitalCoproductNaturality.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom040` and `OAIQ368Chrom041` of this split; the published statement `OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom046`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom040
import Definitions.Def_OAIQ368Chrom041
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_globalCoproduct_mul

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PointEvaluation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def clearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ)
    (f : sourceFiltration a c η hc θ T.dim W) :
    MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) :=
  Classical.choose (totalLeadingPolynomial_denominator_divisible a c η hc θ T hT W f.val f.property
    T.centerPairs T.centerPairs_ne T.centerPairs_norev hχ)

lemma denominator_clearedLeading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) (f : sourceFiltration a c η hc θ T.dim W) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerDenominator a T T.centerPairs) * clearedLeading a c η hc θ T hT hχ W f =
      totalLeadingPolynomial a c η hc θ T hT W f.val :=
  (Classical.choose_spec (totalLeadingPolynomial_denominator_divisible a c η hc θ T hT W f.val f.property
    T.centerPairs T.centerPairs_ne T.centerPairs_norev hχ)).symm

noncomputable def clearedLeadingMap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) :
    sourceFiltration a c η hc θ T.dim W →ₗ[ℚ]
      MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) where
  toFun := clearedLeading a c η hc θ T hT hχ W
  map_add' f g := by
    apply scalar_mul_injective _ (centerDenominator_ne_zero a T)
    dsimp only
    rw [mul_add,denominator_clearedLeading,denominator_clearedLeading,denominator_clearedLeading]
    simp only [totalLeadingPolynomial,Submodule.coe_add,map_add]
  map_smul' r f := by
    apply scalar_mul_injective _ (centerDenominator_ne_zero a T)
    dsimp only
    rw [mul_smul_comm,denominator_clearedLeading,denominator_clearedLeading]
    simp only [totalLeadingPolynomial,Submodule.coe_smul,map_smul,RingHom.id_apply]

noncomputable def normalizedSymbol (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (hχ : T.PairSymmetric a) (W : ℤ) :
    sourceFiltration a c η hc θ T.dim W →ₗ[ℚ]
      MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) :=
  (LinearMap.mulLeft ℚ (map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
    (centerNumerator a T T.centerPairs))).comp (clearedLeadingMap a c η hc θ T hT hχ W)

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalCoproductUnits
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
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace Regroup

lemma totalLeadingPolynomial_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    totalLeadingPolynomial a c η hc θ U hU W
        (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (totalLeadingPolynomial a c η hc θ T hT W f) := by
  unfold totalLeadingPolynomial
  rw [centeredRestrictionB_natural]
  exact mapLinear_extendPolynomial _ _ _ _ (fun x=>(weightComponent_natural a _ e W x).symm) _

lemma clearedLeading_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (hχT : T.PairSymmetric a) (hχU : U.PairSymmetric a) (W : ℤ)
    (f : sourceFiltration a c η hc θ T.dim W) :
    clearedLeading a c η hc θ U hU hχU W
        (filtrationDimensionEquiv a c η hc θ e.dimension W f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (clearedLeading a c η hc θ T hT hχT W f) := by
  apply scalar_mul_injective _ (centerDenominator_ne_zero a U)
  dsimp only
  rw [denominator_clearedLeading,filtrationDimensionEquiv_val,totalLeadingPolynomial_natural]
  conv_rhs => lhs; rw [←centerDenominator_natural a e he]
  rw [←extendPolynomial_map_algebra
    (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom e.centers,
    ←map_mul,denominator_clearedLeading]

lemma normalizedSymbol_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (he : e.OrderPreserving) (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ)
    (hχT : T.PairSymmetric a) (hχU : U.PairSymmetric a) (W : ℤ)
    (f : sourceFiltration a c η hc θ T.dim W) :
    normalizedSymbol a c η hc θ U hU hχU W
        (filtrationDimensionEquiv a c η hc θ e.dimension W f)=
      extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
        e.centers (normalizedSymbol a c η hc θ T hT hχT W f) := by
  change map _ (centerNumerator a U U.centerPairs)*clearedLeading a c η hc θ U hU hχU W _=
    extendPolynomial _ _ (map _ (centerNumerator a T T.centerPairs)*clearedLeading a c η hc θ T hT hχT W f)
  rw [clearedLeading_natural a c η hc θ e he hT hU hχT hχU W f,map_mul,
    extendPolynomial_map_algebra,centerNumerator_natural a e he]

end Regroup
end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

lemma globalSplitCoproduct_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k (slopeSplitZeroLeft c η hc θ k.1) x=
      globalUnit a c η hc θ⊗ₜ[ℚ]DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x := by
  rw [globalSplitCoproduct_dimensions a c η hc θ k
    (slopeSplitZeroLeft c η hc θ k.1) 0 k.1.val rfl (right_ofPair 0 k.1.val (zero_add _))
    (show OnSlopeOrZero c η θ 0 from (0 : slopeDimensions c η hc θ).property) k.1.property (zero_add _) x]
  rw [unitalGradeCoproduct_zero_left,globalTensorGradeInclusion_part]
  erw [unitalLof_cast]
  rfl

lemma globalSplitCoproduct_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k (slopeSplitZeroRight c η hc θ k.1) x=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]globalUnit a c η hc θ := by
  rw [globalSplitCoproduct_dimensions a c η hc θ k
    (slopeSplitZeroRight c η hc θ k.1) k.1.val 0 rfl (right_ofPair k.1.val 0 (add_zero _))
    k.1.property (show OnSlopeOrZero c η θ 0 from (0 : slopeDimensions c η hc θ).property) (add_zero _) x]
  rw [unitalGradeCoproduct_zero_right,globalTensorGradeInclusion_part]
  exact congrArg (fun z=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]z)
    (globalLof_gradeOne_cast a c η hc θ (k.2-k.2) (sub_self _).symm)

lemma globalCoproduct_counit_left_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map (globalCounit a c η hc θ) LinearMap.id
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      (1:ℚ)⊗ₜ[ℚ]DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x := by
  rw [globalCoproduct_lof,map_sum,Finset.sum_eq_single (slopeSplitZeroLeft c η hc θ k.1)]
  · rw [globalSplitCoproduct_zero_left,TensorProduct.map_tmul,globalCounit_unit,LinearMap.id_apply]
  · intro s _ hs
    exact globalCounit_tensor_nonzero_left a c η hc θ ⟨left s.val,s.property.1⟩
      ⟨right s.val,s.property.2⟩ (slopeSplit_ne_left_zero c η hc θ k.1 s hs) k.2 _
  · intro hs
    exact False.elim (hs (Finset.mem_univ _))

lemma globalCoproduct_counit_right_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map LinearMap.id (globalCounit a c η hc θ)
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ](1:ℚ) := by
  rw [globalCoproduct_lof,map_sum,Finset.sum_eq_single (slopeSplitZeroRight c η hc θ k.1)]
  · rw [globalSplitCoproduct_zero_right,TensorProduct.map_tmul,globalCounit_unit,LinearMap.id_apply]
  · intro s _ hs
    exact globalCounit_tensor_nonzero_right a c η hc θ ⟨left s.val,s.property.1⟩
      ⟨right s.val,s.property.2⟩ (slopeSplit_ne_right_zero c η hc θ k.1 s hs) k.2 _
  · intro hs
    exact False.elim (hs (Finset.mem_univ _))

lemma globalCoproduct_counit_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (x : UnitalShuffle a c η hc θ) :
    TensorProduct.map (globalCounit a c η hc θ) LinearMap.id (globalCoproduct a c η hc θ x)=
      (1:ℚ)⊗ₜ[ℚ]x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero,TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add,hx,hy,TensorProduct.tmul_add]
  | of k x => exact globalCoproduct_counit_left_lof a c η hc θ k x

lemma globalCoproduct_counit_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (x : UnitalShuffle a c η hc θ) :
    TensorProduct.map LinearMap.id (globalCounit a c η hc θ) (globalCoproduct a c η hc θ x)=
      x⊗ₜ[ℚ](1:ℚ) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero,TensorProduct.zero_tmul]
  | add x y hx hy => simp only [map_add,hx,hy,TensorProduct.add_tmul]
  | of k x => exact globalCoproduct_counit_right_lof a c η hc θ k x

lemma globalCoproduct_unit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) :
    globalCoproduct a c η hc θ (globalUnit a c η hc θ)=
      globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ := by
  change globalCoproduct a c η hc θ
    (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (0,0) (unitalGradeOne a c η hc θ))=_
  rw [globalCoproduct_lof]
  have hh := Finset.sum_eq_single (s:=Finset.univ) (slopeSplitZeroLeft c η hc θ 0)
    (f:=fun s : SlopeSplit c η hc θ (0 : slopeDimensions c η hc θ).val=>
      globalSplitCoproduct a c η hc θ (0,0) s (unitalGradeOne a c η hc θ))
  rw [hh]
  · exact globalSplitCoproduct_zero_left a c η hc θ 0 _
  · intro s _ hs
    have hz : left s.val=0 := by
      funext i
      have hi := congrFun (left_add_right s.val) i
      change left s.val i+right s.val i=0 at hi
      exact (Nat.add_eq_zero_iff.mp hi).1
    exact False.elim ((slopeSplit_ne_left_zero c η hc θ 0 s hs) hz)
  · intro hs
    exact False.elim (hs (Finset.mem_univ _))
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
lemma unitalSeparationConstant_zero_left_any (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (d : I → ℕ) (x : B a (slope c η) (0+d)) :
    unitalSeparationConstant a c η hc 0 d (Or.inl rfl) x=
      (1:B a (slope c η) 0)⊗ₜ[ℚ]castB a (slope c η) (zero_add d) x := by
  have h := unitalSeparationConstant_zero_left a c η hc d
    (castB a (slope c η) (zero_add d) x)
  simpa only [castB_trans,castB_rfl] using h

lemma unitalSeparationConstant_map_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (e f : I → ℕ)
    (x : B a (slope c η) (0+e)⊗[ℚ]B a (slope c η) f) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc 0 e (Or.inl rfl)) LinearMap.id x)=
      (1:B a (slope c η) 0)⊗ₜ[ℚ]
        TensorProduct.map (castBLinear a (slope c η) (zero_add e)) LinearMap.id x := by
  apply TensorTransport.map_left_insert
  intro y
  rw [castBLinear_apply]
  exact unitalSeparationConstant_zero_left_any a c η hc e y

lemma unitalCoproduct_coassoc_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (e f : I → ℕ)
    (he : OnSlopeOrZero c η θ e) (hf : OnSlopeOrZero c η θ f)
    (x : B a (slope c η) ((0+e)+f)) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc 0 e (Or.inl rfl)) LinearMap.id
        (unitalSeparationConstant a c η hc (0+e) f
          ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc he |>.compatible hf) x))=
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc 0 (e+f) (Or.inl rfl)
          (castB a (slope c η) (add_assoc 0 e f) x)) := by
  rw [unitalSeparationConstant_map_zero_left]
  have h := unitalSeparationConstant_cast a c η hc (zero_add e) (rfl : f=f)
    ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc he |>.compatible hf) (he.compatible hf) x
  simp only [castBLinear_rfl] at h ⊢
  rw [←h]
  rw [unitalSeparationConstant_zero_left_any,TensorProduct.map_tmul,LinearMap.id_apply,
    castB_trans]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalShuffleCoalgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def globalCoproductAlgHom (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)] :
    UnitalShuffle a c η hc θ →ₐ[ℚ] SignedGlobalTensor a c η hc θ :=
  AlgHom.ofLinearMap (globalCoproduct a c η hc θ)
    (globalCoproduct_unit a c η hc θ) (globalCoproduct_mul a c η hc θ)
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

lemma zeroDimension_lof_scalar (k : SlopeWeight c η hc θ) (h : k.1.val=0)
    (x : unitalComponent a c η hc θ k) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x =
      globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x) •
        globalUnit a c η hc θ := by
  rcases k with ⟨⟨d,hd⟩,W⟩
  dsimp at h
  subst d
  by_cases hW : W=0
  · subst W
    change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 x =
      globalCounit a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0 x) •
        globalUnit a c η hc θ
    rw [globalCounit_lof_zero,globalUnit,←map_smul]
    exact congrArg (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) 0)
      (zeroGrade_eq_scalar a c η hc θ x)
  · let := zeroUnitalGrade_subsingleton a c η hc θ W hW
    have hx : x=0 := Subsingleton.elim _ _
    simp only [hx,map_zero,zero_smul]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalSeriesEvaluation
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

lemma globalPrimitive_counit {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) : globalCounit a c η hc θ x=0 := by
  have h := globalCoproduct_counit_left a c η hc θ x
  rw [(mem_globalPrimitives a c η hc θ x).mp hx,map_add,
    TensorProduct.map_tmul,TensorProduct.map_tmul,globalCounit_unit,
    LinearMap.id_apply,LinearMap.id_apply] at h
  have he := congrArg (fun t=>globalCounit a c η hc θ
    (TensorProduct.lid ℚ (UnitalShuffle a c η hc θ) t)) h
  simp only [map_add,TensorProduct.lid_tmul,map_smul,globalCounit_unit,smul_eq_mul,
    mul_one,one_mul] at he
  exact add_eq_right.mp he

end ElementaryPositivity.RawShuffle

end

end OAI
end


