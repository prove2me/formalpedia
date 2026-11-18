-- Prove2me | Definitions.Def_OAIQ368Chrom023
-- name    : OAIQ368Chrom023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:18:58.668207+00:00
-- url     : https://prove2.me/theorems/b476d620-8ca8-4848-9168-c4c689b1c0ce
-- title:
--   Definitions bundle OAIQ368Chrom023 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 33 definitions and 11 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.braidFourAlg`, `OAI.ElementaryPositivity.RawShuffle.braidFourM`, `OAI.ElementaryPositivity.RawShuffle.braidFourN`, `OAI.ElementaryPositivity.RawShuffle.braidFourRing`, `OAI.ElementaryPositivity.RawShuffle.braidFourTensor`, `OAI.ElementaryPositivity.RawShuffle.braidFourTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.braidFourTensorM`, `OAI.ElementaryPositivity.RawShuffle.braidFourTensorN`, `OAI.ElementaryPositivity.RawShuffle.cellSepFourModule`, `OAI.ElementaryPositivity.RawShuffle.cellSepFourNonAssoc`, `OAI.ElementaryPositivity.RawShuffle.cellSepFourSemiring`, `OAI.ElementaryPositivity.RawShuffle.cellSepTensorNonAssoc`, `OAI.ElementaryPositivity.RawShuffle.cellSepTensorSemiring`, `OAI.ElementaryPositivity.RawShuffle.clearBTensorB`, `OAI.ElementaryPositivity.RawShuffle.clearBTensorBA`, `OAI.ElementaryPositivity.RawShuffle.clearedSepTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.clearedSepTensorRing`, `OAI.ElementaryPositivity.RawShuffle.cocommTensorBAlgebra`, `OAI.ElementaryPositivity.RawShuffle.cocommTensorBCommRing`, `OAI.ElementaryPositivity.RawShuffle.dimensionEquivB`, `OAI.ElementaryPositivity.RawShuffle.pairAdd`, `OAI.ElementaryPositivity.RawShuffle.restrictionBUnit`, `OAI.ElementaryPositivity.RawShuffle.restrictionTest`, `OAI.ElementaryPositivity.RawShuffle.slopeDimensions`, `OAI.ElementaryPositivity.RawShuffle.sourceFiltration`, `OAI.ElementaryPositivity.RawShuffle.sourceTensorFiltration`, `OAI.ElementaryPositivity.RawShuffle.sourceTripleFiltration`, `OAI.ElementaryPositivity.RawShuffle.tripleAdd`, `OAI.ElementaryPositivity.RawShuffle.tripleFilterAdd`, `OAI.ElementaryPositivity.RawShuffle.unitalSepTensor`, `OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA`, `OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM`, `OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_ClearedSeparation`, `Chromatic_QuantumTorus_ProductUnitFiltration`, `Chromatic_Shuffle_CellSeparation`, `Chromatic_Shuffle_ClearedSeparationB`, `Chromatic_Shuffle_FourBraiding`, `Chromatic_Shuffle_HNZeroRows`, `Chromatic_Shuffle_Interaction`, `Chromatic_Shuffle_PolynomialExtendInjective`, `Chromatic_Shuffle_Restriction`, `Chromatic_Shuffle_TensorFiltration`, `Chromatic_Shuffle_TensorSymbolSwap`, `Chromatic_Shuffle_TripleFiltration`, `Chromatic_Shuffle_UnitalGradeAlgebra`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom026`, `OAIQ368Chrom027` and `OAIQ368Chrom033`; the statement `OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure`; the proofs of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom022

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def dimensionEquivB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) : B a μ d ≃ₐ[ℚ] B a μ e := by
  subst e
  exact AlgEquiv.refl

noncomputable def restrictionTest (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d : I → ℕ} (T : SplitTree I) (hs : T.OnSlope c η θ) (hd : T.dim=d)
    (k : T.Degrees) (z : T.Centers →₀ ℕ) :
    B a (SlopeArithmetic.slope c η) d →ₗ[ℚ]
      SplitTree.tensor (SplitTree.quotientFamily a (SlopeArithmetic.slope c η)) T :=
  (SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k).comp
    (((MvPolynomial.lcoeff _ z).restrictScalars ℚ).comp
      ((SplitTree.centeredRestrictionB a c η hc θ T hs).toLinearMap.comp
        (dimensionEquivB a (SlopeArithmetic.slope c η) hd.symm).toLinearMap))

noncomputable def sourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Submodule ℚ (B a (SlopeArithmetic.slope c η) d) where
  carrier := {f | ∀ (T : SplitTree I), T.IsOrderedList → ∀ (hs : T.OnSlope c η θ)
    (hd : T.dim=d) (k : T.Degrees) (z : T.Centers →₀ ℕ),
    2*T.totalDegree k+T.doubleShift a<W → restrictionTest a c η hc θ T hs hd k z f=0}
  zero_mem' := by
    intro T hT hs hd k z hw
    exact (restrictionTest a c η hc θ T hs hd k z).map_zero
  add_mem' := by
    intro f g hf hg T hT hs hd k z hw
    rw [map_add,hf T hT hs hd k z hw,hg T hT hs hd k z hw,add_zero]
  smul_mem' := by
    intro r f hf T hT hs hd k z hw
    rw [map_smul,hf T hT hs hd k z hw,smul_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorFiltration
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
open ElementaryPositivity.LinearDetection
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def sourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    Submodule ℚ (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  additiveTensorFiltration (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e) W

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_ClearedSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance clearedSepTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearedSepTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Restriction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma labeledPolynomial_cast {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
    {d e : I → ℕ} (h : d=e) (f : S d) :
    labeledPolynomial (A:=A) (castS h f)=labeledPolynomial f := by
  subst e
  rfl

omit [DecidableEq I] in
lemma labeledPolynomial_full (d : I → ℕ) (f : S d) :
    labeledPolynomial (A:=fun i=>Fin (d i)) f (fun _=>Finset.univ)=f.val := by
  let r : Realization d (A:=fun i=>Fin (d i)) (fun _=>Finset.univ) :=
    fun _=>(Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm
  rw [labeledPolynomial_eq r]
  have hr : realizationMap r=id := rfl
  rw [hr,rename_id]
  rfl

omit [DecidableEq I] in
lemma rightInput_zero_rename {e : I → ℕ} (A : Cut 0 e) (f : S e) :
    rename (rightInput A) f.val=(castS (zero_add e).symm f).val := by
  classical
  have hempty : ∀ i,(A i).val=∅ := fun i=>Finset.card_eq_zero.mp (A i).property
  have huniv : ∀ i,(A i).valᶜ=Finset.univ := by intro i; rw [hempty]; exact Finset.compl_empty
  let r : Realization e (A:=fun i=>Fin ((0+e) i)) (fun _=>Finset.univ) :=
    fun i=>(rightEnum A i).trans (Equiv.subtypeEquivRight (fun x=>by rw [huniv]))
  have hr : realizationMap r=rightInput A := rfl
  rw [←hr,←labeledPolynomial_eq r,←labeledPolynomial_cast (zero_add e).symm f,
    labeledPolynomial_full]

omit [DecidableEq I] in
lemma leftInput_zero_rename {d : I → ℕ} (A : Cut d 0) (f : S d) :
    rename (leftInput A) f.val=(castS (add_zero d).symm f).val := by
  classical
  have huniv : ∀ i,(A i).val=Finset.univ := by
    intro i
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin,Pi.zero_apply,Nat.add_zero] using (A i).property
  let r : Realization d (A:=fun i=>Fin ((d+0) i)) (fun _=>Finset.univ) :=
    fun i=>(leftEnum A i).trans (Equiv.subtypeEquivRight (fun x=>by rw [huniv]))
  have hr : realizationMap r=leftInput A := rfl
  rw [←hr,←labeledPolynomial_eq r,←labeledPolynomial_cast (add_zero d).symm f,
    labeledPolynomial_full]

lemma restrictTensor_zero_left {e : I → ℕ} (A : Cut 0 e) (f : S e) :
    restrictTensor A (castS (zero_add e).symm f)=(1 : S 0)⊗ₜ[ℚ]f := by
  apply tensorValue_injective
  rw [tensorValue_restrictTensor,tensorValue_tmul,OneMemClass.coe_one,map_one,one_mul]
  apply rename_injective (cutSplit A) (cutSplit A).injective
  rw [rename_rename,rename_rename]
  have h₁ : cutSplit A ∘ (cutSplit A).symm=id := funext ((cutSplit A).apply_symm_apply)
  have h₂ : cutSplit A ∘ Sum.inr=rightInput A := rfl
  rw [h₁,h₂,rename_id,rightInput_zero_rename]
  rfl

lemma restrictTensor_zero_right {d : I → ℕ} (A : Cut d 0) (f : S d) :
    restrictTensor A (castS (add_zero d).symm f)=f⊗ₜ[ℚ](1 : S 0) := by
  apply tensorValue_injective
  rw [tensorValue_restrictTensor,tensorValue_tmul,OneMemClass.coe_one,map_one,mul_one]
  apply rename_injective (cutSplit A) (cutSplit A).injective
  rw [rename_rename,rename_rename]
  have h₁ : cutSplit A ∘ (cutSplit A).symm=id := funext ((cutSplit A).apply_symm_apply)
  have h₂ : cutSplit A ∘ Sum.inl=leftInput A := rfl
  rw [h₁,h₂,rename_id,leftInput_zero_rename]
  rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

@[simp] lemma castB_trans (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d e b : I → ℕ}
    (h : d=e) (k : e=b) (f : B a μ d) : castB a μ k (castB a μ h f)=castB a μ (h.trans k) f := by
  subst e; subst b; rfl

lemma restriction_unit_kills_destabilizing (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A : Cut d e)
    {f : S (d+e)} (hf : f∈destabilizingSpace a (slope c η) (d+e)) :
    quotientTensor a (slope c η) d e (restrictTensor A f)=0 := by
  rcases hs with rfl|rfl|hs
  · have ht : restrictTensor A f=(1 : S 0)⊗ₜ[ℚ]castS (zero_add e) f := by
      simpa only [castS_trans,castS_rfl] using restrictTensor_zero_left A (castS (zero_add e) f)
    rw [ht,quotientTensor_tmul]
    have hz : quotientAlg a (slope c η) e (castS (zero_add e) f)=0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (castS_mem_destabilizing a _ _ hf)
    rw [hz,TensorProduct.tmul_zero]
  · have ht : restrictTensor A f=castS (add_zero d) f⊗ₜ[ℚ](1 : S 0) := by
      simpa only [castS_trans,castS_rfl] using restrictTensor_zero_right A (castS (add_zero d) f)
    rw [ht,quotientTensor_tmul]
    have hz : quotientAlg a (slope c η) d (castS (add_zero d) f)=0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (castS_mem_destabilizing a _ _ hf)
    rw [hz,TensorProduct.zero_tmul]
  · exact restriction_kills_destabilizingSpace a c η hc hs A hf

noncomputable def restrictionBUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A : Cut d e) :
    B a (slope c η) (d+e) →ₐ[ℚ] B a (slope c η) d⊗[ℚ]B a (slope c η) e :=
  Ideal.Quotient.liftₐ (destabilizingIdeal a (slope c η) (d+e))
    ((quotientTensor a (slope c η) d e).comp (restrictTensorAlg A))
    (by intro f hf; exact restriction_unit_kills_destabilizing a c η hc hs A hf)

@[simp] lemma restrictionBUnit_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A : Cut d e) (f : S (d+e)) :
    restrictionBUnit a c η hc hs A (quotientAlg a (slope c η) (d+e) f)=
    quotientTensor a (slope c η) d e (restrictTensor A f) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing

noncomputable local instance cellSepTensorSemiring (d e : I → ℕ) : Semiring (S d⊗[ℚ]S e) :=
  (cancelTensorRing d e).toSemiring
noncomputable local instance cellSepTensorNonAssoc (d e : I → ℕ) : NonAssocSemiring (S d⊗[ℚ]S e) :=
  (cancelTensorRing d e).toNonAssocSemiring
noncomputable local instance cellSepFourSemiring (d₁ e₁ d₂ e₂ : I → ℕ) :
    Semiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (cancelFourRing d₁ e₁ d₂ e₂).toSemiring
noncomputable local instance cellSepFourNonAssoc (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (cancelFourRing d₁ e₁ d₂ e₂).toNonAssocSemiring
noncomputable local instance cellSepFourModule (d₁ e₁ d₂ e₂ : I → ℕ) :
    Module ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := Semiring.toModule

end ElementaryPositivity.RawShuffle

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TripleFiltration
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
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def sourceTripleFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e f : I → ℕ) (W : ℤ) :
    Submodule ℚ ((B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) f) :=
  additiveTensorFiltration (sourceTensorFiltration a c η hc θ d e) (sourceFiltration a c η hc θ f) W

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ProductUnitFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma OnSlopeOrZero.add {c η : I → ℝ} (hc : ∀ i,0 < c i) {θ : ℝ} {d e : I → ℕ}
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) :
    OnSlopeOrZero c η θ (d+e) := by
  rcases hd with rfl|hd
  · simpa only [zero_add] using he
  rcases he with rfl|he
  · exact Or.inr (by simpa only [add_zero] using hd)
  exact Or.inr ((slope_add_same c η hc (hd.trans he.symm)).trans hd)
end ElementaryPositivity.SlopeArithmetic

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
noncomputable local instance braidFourTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidFourTensorAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidFourRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance
noncomputable local instance braidFourAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance

noncomputable local instance braidFourTensorN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (braidFourTensor a μ d e).toNonUnitalNonAssocSemiring
noncomputable local instance braidFourTensorM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule
noncomputable local instance braidFourN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring
noncomputable local instance braidFourM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Module ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂))
      ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := Semiring.toModule

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance unitalSepTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance unitalSepTensorA (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance

noncomputable local instance unitalSepTensorN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (unitalSepTensor a μ d e).toNonUnitalNonAssocSemiring
noncomputable local instance unitalSepTensorM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule

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
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance clearBTensorS_rc9d63c_1 (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearBTensorSA_rc9d63c_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearBTensorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance clearBTensorBA (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev slopeDimensions (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) : AddSubmonoid (I → ℕ) where
  carrier := {d | OnSlopeOrZero c η θ d}
  zero_mem' := Or.inl rfl
  add_mem' := fun hd he=>hd.add hc he

end ElementaryPositivity.RawShuffle

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
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance cocommTensorBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d ⊗[ℚ] B a μ e) := inferInstance
noncomputable local instance cocommTensorBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d ⊗[ℚ] B a μ e) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PolynomialExtendInjective
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable local instance pairAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    AddCommGroup (B a μ d⊗[ℚ]B a μ e) := TensorProduct.addCommGroup
noncomputable local instance tripleAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e f : I → ℕ) :
    AddCommGroup ((B a μ d⊗[ℚ]B a μ e)⊗[ℚ]B a μ f) := TensorProduct.addCommGroup
noncomputable local instance tripleFilterAdd (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d e f : I → ℕ) (W : ℤ) :
    AddCommGroup (sourceTripleFiltration a c η hc θ d e f W) := Submodule.addCommGroup _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNZeroRows
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

omit [DecidableEq I] in
include hc in
lemma slopeValue_eq_zero_iff (θ : ℝ) (d : I → ℕ) (hd : d≠0) :
    slopeValue c η θ d=0 ↔ slope c η d=θ := by
  rw [slopeValue,sub_eq_zero,SlopeArithmetic.slope,div_eq_iff (ne_of_gt (mass_pos c hc d hd))]

end
end ElementaryPositivity.RawShuffle

end

end OAI
end


