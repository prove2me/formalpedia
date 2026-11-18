-- Prove2me | Definitions.Def_OAIQ368Chrom041
-- name    : OAIQ368Chrom041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:45:43.332971+00:00
-- url     : https://prove2.me/theorems/1a69412e-e6d1-4ce1-921a-94257d920e30
-- title:
--   Definitions bundle OAIQ368Chrom041 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 9 definitions and 23 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SplitTree.centerPower`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.sourceTensorComm`, `OAI.ElementaryPositivity.RawShuffle.castBLinear`, `OAI.ElementaryPositivity.RawShuffle.leftTripleEquiv`, `OAI.ElementaryPositivity.RawShuffle.leftTripleView`, `OAI.ElementaryPositivity.RawShuffle.slopeSplitSwap`, `OAI.ElementaryPositivity.RawShuffle.slopeSplitZeroLeft`, `OAI.ElementaryPositivity.RawShuffle.slopeSplitZeroRight`, `OAI.ElementaryPositivity.RawShuffle.unitalTensorGradeComm`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalConvolutionQuotient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalConvolutionQuotient.lean), [`Chromatic_Shuffle_GlobalCoproductCoassociative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalCoproductCoassociative.lean), [`Chromatic_Shuffle_GlobalCoproductCocommutative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalCoproductCocommutative.lean), [`Chromatic_Shuffle_GlobalCoproductUnits`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalCoproductUnits.lean), [`Chromatic_Shuffle_GlobalShuffleCoalgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalShuffleCoalgebra.lean), [`Chromatic_Shuffle_GlobalTensorGradeProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalTensorGradeProduct.lean), [`Chromatic_Shuffle_GlobalTripleGradeInclusion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalTripleGradeInclusion.lean), [`Chromatic_Shuffle_SymbolSwap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SymbolSwap.lean), [`Chromatic_Shuffle_TensorSymbolSwap`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TensorSymbolSwap.lean), [`Chromatic_Walls_Grade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/Grade.lean), [`Chromatic_Walls_UnitalCoproductNaturality`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/UnitalCoproductNaturality.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom042`, `OAIQ368Chrom043` and `OAIQ368Chrom045`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom039

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Grade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma zeroUnitalGrade_subsingleton (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (W : ℤ) (hW : W≠0) : Subsingleton (UnitalSourceGrade a c η hc θ 0 W) := by
  unfold UnitalSourceGrade
  by_cases hw : W≤0
  · have hw' : W+1≤0 := by omega
    simpa [unitalSourceFiltration_zero,hw,hw'] using
      grade_same_subsingleton (⊤ : Submodule ℚ (B a (slope c η) 0))
  · have hw' : ¬W+1≤0 := by omega
    simpa [unitalSourceFiltration_zero,hw,hw'] using
      grade_same_subsingleton (⊥ : Submodule ℚ (B a (slope c η) 0))
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymbolSwap
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

noncomputable def centerPower (a : I → I → ℕ) (T : SplitTree I) (φ : ℤ → ℕ) :
    MvPolynomial T.Centers ℚ :=
  ∏ ij∈T.centerPairs,diagonal ij.1 ij.2 ^ φ (eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2))

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

noncomputable def sourceTensorComm (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    sourceTensorFiltration a c η hc θ d e W ≃ₗ[ℚ] sourceTensorFiltration a c η hc θ e d W :=
  tensorFiltrationComm (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e) W

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def unitalTensorGradeComm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d e W →ₗ[ℚ]
      UnitalSourceTensorGrade a c η hc θ e d W :=
  tensorGradeComm (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e) W

lemma unitalTensorGradeComm_part (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ) (W u : ℤ)
    (x : UnitalSourceGrade a c η hc θ d u)
    (y : UnitalSourceGrade a c η hc θ e (W-u)) :
    unitalTensorGradeComm a c η hc θ d e W
      (unitalTensorGradeInclusionW a c η hc θ d e W u (x⊗ₜ[ℚ]y))=
      unitalTensorGradeInclusionW a c η hc θ e d W (W-u)
        (y⊗ₜ[ℚ]unitalGradeCast a c η hc θ rfl (show u=W-(W-u) by omega) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      simp only [unitalTensorGradeInclusionW,unitalGradeCast_mk,
        unitalTensorGradeComm]
      apply congrArg (mk _ _)
      apply Subtype.ext
      change y.val⊗ₜ[ℚ]x.val=y.val⊗ₜ[ℚ](unitalFiltrationCast a c η hc θ rfl _ x).val
      rw [unitalFiltrationCast_val,castB_rfl]

lemma globalTensorGradeInclusion_comm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalTensorGradeInclusion a c η hc θ e d W (unitalTensorGradeComm a c η hc θ d.val e.val W x)=
      TensorProduct.comm ℚ _ _ (globalTensorGradeInclusion a c η hc θ d e W x) := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht u x y =>
    rw [unitalTensorGradeComm_part,globalTensorGradeInclusion_part,globalTensorGradeInclusion_part,
      TensorProduct.comm_tmul,unitalLof_cast a c η hc θ (d:=d) (e:=d)]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCocommutative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
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

noncomputable def slopeSplitSwap (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    SlopeSplit c η hc θ d ≃ SlopeSplit c η hc θ d where
  toFun s:=⟨DimensionSplit.swap s.val,by simpa only [left_swap,right_swap] using s.property.symm⟩
  invFun s:=⟨DimensionSplit.swap s.val,by simpa only [left_swap,right_swap] using s.property.symm⟩
  left_inv s:=by apply Subtype.ext; exact swap_swap s.val
  right_inv s:=by apply Subtype.ext; exact swap_swap s.val

lemma globalSplitCoproduct_dimensions (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (d e : I → ℕ)
    (hd : left s.val=d) (he : right s.val=e)
    (hds : OnSlopeOrZero c η θ d) (hes : OnSlopeOrZero c η θ e)
    (h : d+e=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k s x=
      globalTensorGradeInclusion a c η hc θ ⟨d,hds⟩ ⟨e,hes⟩ k.2
        (unitalGradeCoproduct a c η hc θ d e (hds.compatible hes) k.2
          (unitalGradeCast a c η hc θ h.symm rfl x)) := by
  subst d; subst e
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_UnitalCoproductNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
noncomputable def castBLinear (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) : B a μ d →ₗ[ℚ] B a μ e := by
  subst e
  exact LinearMap.id

lemma castBLinear_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) (x : B a μ d) :
    castBLinear a μ h x=castB a μ h x := by subst e; rfl

lemma castBLinear_rfl (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    castBLinear a μ (rfl : d=d)=LinearMap.id := rfl

lemma unitalSeparationConstant_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) {d e d' e' : I → ℕ} (hd : d=d') (he : e=e')
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (hs' : d'=0 ∨ e'=0 ∨ slope c η d'=slope c η e')
    (x : B a (slope c η) (d+e)) :
    unitalSeparationConstant a c η hc d' e' hs'
      (castB a (slope c η) (congrArg₂ (·+·) hd he) x)=
    TensorProduct.map (castBLinear a (slope c η) hd) (castBLinear a (slope c η) he)
      (unitalSeparationConstant a c η hc d e hs x) := by
  subst d'; subst e'
  simp only [castB_rfl,castBLinear_rfl,TensorProduct.map_id,LinearMap.id_apply]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTripleGradeInclusion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
  ElementaryPositivity.LinearDetection DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalTripleGrade_right_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val (e.val+f.val) W) :
    globalTripleGradeRight a c η hc θ d e f W
      (unitalTensorCoproductRight a c η hc θ d.val e.val f.val (e.property.compatible f.property) W x)=
      tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
        (unitalSourceFiltration a c η hc θ (e.val+f.val))
        (unitalSourceFiltration_antitone a c η hc θ d.val)
        (unitalSourceFiltration_antitone a c η hc θ (e.val+f.val))
        (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u))
        (fun u=>(globalTensorGradeInclusion a c η hc θ e f u).comp
          (unitalGradeCoproduct a c η hc θ e.val f.val (e.property.compatible f.property) u)) W x := by
  have H := tensorGradeLift_map_natural
    (unitalSourceFiltration a c η hc θ d.val)
    (unitalSourceFiltration a c η hc θ (e.val+f.val))
    (unitalSourceFiltration a c η hc θ d.val)
    (unitalSourceTensorFiltration a c η hc θ e.val f.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ (e.val+f.val))
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceTensorFiltration_antitone a c η hc θ e.val f.val)
    LinearMap.id
    (unitalSeparationConstant a c η hc e.val f.val (e.property.compatible f.property))
    (fun _ _ h=>h)
    (unitalSeparationConstant_filtered a c η hc θ e.val f.val (e.property.compatible f.property))
    (fun u=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u))
    (globalTensorGradeInclusion a c η hc θ e f) W x
  simp only [gradeMap_id] at H
  exact H

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

def leftTripleView (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : LeftSlopeTriple c η hc θ d) : SlopeTriple c η hc θ d :=
  ⟨(left p.2.val,right p.2.val,right p.1.val),by
    exact ⟨by rw [left_add_right,left_add_right],p.2.property.1,p.2.property.2,p.1.property.2⟩⟩

omit [DecidableEq I] in
lemma leftTripleView_injective (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    Function.Injective (leftTripleView c η hc θ d) := by
  rintro ⟨s,t⟩ ⟨s',t'⟩ h
  have h1 : left t.val=left t'.val := congrArg (fun p=>p.val.1) h
  have h2 : right t.val=right t'.val := congrArg (fun p=>p.val.2.1) h
  have hs : s=s' := by
    apply Subtype.ext
    apply DimensionSplit.ext
    rw [←left_add_right t.val,←left_add_right t'.val,h1,h2]
  subst s'
  have ht : t=t' := Subtype.ext (DimensionSplit.ext h1)
  subst t'
  rfl

omit [DecidableEq I] in
lemma leftTripleView_surjective (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    Function.Surjective (leftTripleView c η hc θ d) := by
  rintro ⟨⟨a,b,f⟩,hs,ha,hb,hf⟩
  let s : SlopeSplit c η hc θ d :=
    ⟨ofPair (a+b) f hs,by simpa only [left_ofPair,right_ofPair] using And.intro (ha.add hc hb) hf⟩
  let t : SlopeSplit c η hc θ (a+b) :=
    ⟨ofPair a b (rfl : a+b=a+b),by simpa only [left_ofPair,right_ofPair] using And.intro ha hb⟩
  refine ⟨⟨s,t⟩,?_⟩
  apply Subtype.ext
  change (left (ofPair a b rfl),right (ofPair a b rfl),right (ofPair (a+b) f hs))=(a,b,f)
  simp only [left_ofPair,right_ofPair]

noncomputable def leftTripleEquiv (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :
    LeftSlopeTriple c η hc θ d ≃ SlopeTriple c η hc θ d :=
  Equiv.ofBijective (leftTripleView c η hc θ d)
    ⟨leftTripleView_injective c η hc θ d,leftTripleView_surjective c η hc θ d⟩

omit [DecidableEq I] in
lemma leftTripleView_build (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : SlopeTriple c η hc θ d) :
    leftTripleView c η hc θ d (leftTripleBuild c η hc θ d p)=p := by
  apply Subtype.ext
  simp only [leftTripleView,leftTripleBuild,left_ofPair,right_ofPair]

omit [DecidableEq I] in
lemma leftTripleBuild_view (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ)
    (p : LeftSlopeTriple c η hc θ d) :
    leftTripleBuild c η hc θ d (leftTripleView c η hc θ d p)=p :=
  leftTripleView_injective c η hc θ d (leftTripleView_build c η hc θ d _)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductCoassociative
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma globalTripleGrade_right_cast_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val (e.val+f.val) W) :
    tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
        (unitalSourceFiltration a c η hc θ (e.val+f.val))
        (unitalSourceFiltration_antitone a c η hc θ d.val)
        (unitalSourceFiltration_antitone a c η hc θ (e.val+f.val))
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,v))
        (fun u=>(globalTensorGradeInclusion a c η hc θ e f u).comp
          ((unitalGradeCoproduct a c η hc θ e.val f.val (e.property.compatible f.property) u).comp
            (unitalGradeCast a c η hc θ rfl rfl).toLinearMap)) W x=
    globalTripleGradeRight a c η hc θ d e f W
      (unitalTensorCoproductRight a c η hc θ d.val e.val f.val (e.property.compatible f.property) W x) := by
  rw [globalTensorGrade_coproduct_family_cast]
  exact (globalTripleGrade_right_natural a c η hc θ d e f W x).symm

lemma globalIteratedRightSplit_dimensions (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (right s.val))
    (b d e f : I → ℕ) (hb : right s.val=b) (hd : left s.val=d)
    (he : left t.val=e) (hf : right t.val=f)
    (hbs : OnSlopeOrZero c η θ b) (hds : OnSlopeOrZero c η θ d)
    (hes : OnSlopeOrZero c η θ e) (hfs : OnSlopeOrZero c η θ f)
    (hef : e+f=b) (hdb : d+b=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k s t x =
      tensorGradeLift (unitalSourceFiltration a c η hc θ d)
        (unitalSourceFiltration a c η hc θ b)
        (unitalSourceFiltration_antitone a c η hc θ d)
        (unitalSourceFiltration_antitone a c η hc θ b)
        (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨d,hds⟩,v))
        (fun u=>(globalTensorGradeInclusion a c η hc θ ⟨e,hes⟩ ⟨f,hfs⟩ u).comp
          ((unitalGradeCoproduct a c η hc θ e f (hes.compatible hfs) u).comp
            (unitalGradeCast a c η hc θ hef.symm rfl).toLinearMap)) k.2
        (unitalGradeCoproduct a c η hc θ d b (hds.compatible hbs) k.2
          (unitalGradeCast a c η hc θ hdb.symm rfl x)) := by
  subst b; subst d; subst e; subst f
  rfl

lemma globalIteratedRightSplit_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (right s.val))
    (d e f : slopeDimensions c η hc θ)
    (hb : right s.val=e.val+f.val) (hd : left s.val=d.val)
    (he : left t.val=e.val) (hf : right t.val=f.val)
    (hp : d.val+(e.val+f.val)=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalIteratedRightSplit a c η hc θ k s t x=
    globalTripleGradeRight a c η hc θ d e f k.2
      (unitalTensorCoproductRight a c η hc θ d.val e.val f.val (e.property.compatible f.property) k.2
        (unitalGradeCoproduct a c η hc θ d.val (e.val+f.val)
          (d.property.compatible (e.property.add hc f.property)) k.2
          (unitalGradeCast a c η hc θ hp.symm rfl x))) := by
  rw [globalIteratedRightSplit_dimensions a c η hc θ k s t (e.val+f.val) d.val e.val f.val
    hb hd he hf (e.property.add hc f.property) d.property e.property f.property rfl hp x]
  exact globalTripleGrade_right_cast_natural a c η hc θ d e f k.2 _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalCoproductUnits
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

noncomputable def slopeSplitZeroLeft (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) : SlopeSplit c η hc θ d.val :=
  ⟨ofPair 0 d.val (zero_add _),by
    constructor
    · exact Or.inl rfl
    · rw [right_ofPair]
      exact d.property⟩
noncomputable def slopeSplitZeroRight (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) : SlopeSplit c η hc θ d.val :=
  ⟨ofPair d.val 0 (add_zero _),by
    constructor
    · exact d.property
    · rw [right_ofPair]
      exact Or.inl rfl⟩

omit [DecidableEq I] in
lemma slopeSplit_ne_left_zero (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) (s : SlopeSplit c η hc θ d.val)
    (h : s≠slopeSplitZeroLeft c η hc θ d) : left s.val≠0 := by
  intro hz
  apply h
  exact Subtype.ext (DimensionSplit.ext hz)
omit [DecidableEq I] in
lemma slopeSplit_ne_right_zero (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) (s : SlopeSplit c η hc θ d.val)
    (h : s≠slopeSplitZeroRight c η hc θ d) : right s.val≠0 := by
  intro hz
  apply h
  apply Subtype.ext
  apply DimensionSplit.ext
  change left s.val=d.val
  simpa only [hz,add_zero] using left_add_right s.val

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalShuffleCoalgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
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

omit [DecidableEq I] in
lemma dimensionSize_add (d e : I → ℕ) : dimensionSize (d+e)=dimensionSize d+dimensionSize e :=
  Finset.sum_add_distrib

omit [DecidableEq I] in
lemma dimensionSize_eq_zero (d : I → ℕ) : dimensionSize d=0 ↔ d=0 := by
  simp only [dimensionSize,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies]
  exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩

variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {A : Type*} [Ring A] [Algebra ℚ A]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_zero (f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)) :
    convVanishes a c η hc θ 0 f := by
  intro k hk
  omega

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_mono {n m : ℕ} (h : n ≤ m)
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ m f) : convVanishes a c η hc θ n f :=
  fun k hk=>hf k (lt_of_lt_of_le hk h)

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalTensorGrade_map_vanishes (n m : ℕ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A))
    (hf : convVanishes a c η hc θ n f) (hg : convVanishes a c η hc θ m g)
    (d e : slopeDimensions c η hc θ) (h : dimensionSize d.val+dimensionSize e.val < n+m)
    (W : ℤ) (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map f.ofConv g.ofConv (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part,TensorProduct.map_tmul]
    by_cases hd : dimensionSize d.val < n
    · rw [hf (d,u) hd x,TensorProduct.zero_tmul]
    · have he : dimensionSize e.val < m := by omega
      rw [hg (e,W-u) he y,TensorProduct.tmul_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalConvolutionQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
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

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma convVanishes_neg {n : ℕ}
    {f : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] A)}
    (hf : convVanishes a c η hc θ n f) : convVanishes a c η hc θ n (-f) := by
  intro k hk x
  change -(f.ofConv _)=0
  rw [hf k hk x,neg_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end


