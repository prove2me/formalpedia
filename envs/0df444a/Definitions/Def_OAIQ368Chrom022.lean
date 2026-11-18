-- Prove2me | Definitions.Def_OAIQ368Chrom022
-- name    : OAIQ368Chrom022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:15:38.846067+00:00
-- url     : https://prove2.me/theorems/ae1177fc-2cbc-40d9-a3a1-60de90a6ca69
-- title:
--   Definitions bundle OAIQ368Chrom022 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 179 declarations of OpenAI's Lean: 59 definitions and 120 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.IsSeparate`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.inverseKernelUnit`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.liftSeparateUnit`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.quotientInverseKernelUnit`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.renameSeries`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient`, `OAI.ElementaryPositivity.RawShuffle.SlopeEulerSymmetric`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.Centers`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.Degrees`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.IsOrderedList`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.NonnegativeDegree`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.OnSlope`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.centerTranslation`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.centeredRestrictionB`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.componentTensor`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.doubleShift`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.quotientFamily`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.restrictionB`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.tensor`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.totalDegree`, `OAI.ElementaryPositivity.RawShuffle.cancelFourAlg`, `OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital`, `OAI.ElementaryPositivity.RawShuffle.cancelFourRing`, `OAI.ElementaryPositivity.RawShuffle.cancelSeriesRing`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorNonUnital`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorSelf`, `OAI.ElementaryPositivity.RawShuffle.canonicalGridPolynomial`, `OAI.ElementaryPositivity.RawShuffle.castB`, `OAI.ElementaryPositivity.RawShuffle.cellAction`, `OAI.ElementaryPositivity.RawShuffle.componentB`, `OAI.ElementaryPositivity.RawShuffle.crossKernelPolynomial`, `OAI.ElementaryPositivity.RawShuffle.cutKernel`, `OAI.ElementaryPositivity.RawShuffle.degreeZeroB`, `OAI.ElementaryPositivity.RawShuffle.doubleTensorShuffle`, `OAI.ElementaryPositivity.RawShuffle.fourGridPolynomial`, `OAI.ElementaryPositivity.RawShuffle.fourPackAction`, `OAI.ElementaryPositivity.RawShuffle.fourPackEquiv` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_Shuffle_CanonicalCard`, `Chromatic_Shuffle_CellVars`, `Chromatic_Shuffle_ComponentB`, `Chromatic_Shuffle_CrossDifference`, `Chromatic_Shuffle_Degree`, `Chromatic_Shuffle_ExtendPolynomial`, `Chromatic_Shuffle_FourTensorKernel`, `Chromatic_Shuffle_GridShapeTensor`, `Chromatic_Shuffle_HNExpansion`, `Chromatic_Shuffle_LabeledPolynomial`, `Chromatic_Shuffle_LaurentKernel`, `Chromatic_Shuffle_Realization`, `Chromatic_Shuffle_Restriction`, `Chromatic_Shuffle_RestrictionB`, `Chromatic_Shuffle_SameDen`, `Chromatic_Shuffle_SeparationCoefficients`, `Chromatic_Shuffle_ShuffleUnits`, `Chromatic_Shuffle_SumPackCut`, `Chromatic_Shuffle_SymbolDetection`, `Chromatic_Shuffle_TargetEmbedding`, `Chromatic_Shuffle_TaylorSCoeffHomogeneous`, `Chromatic_Walls_PolynomialCoeffLinear`, `Chromatic_Walls_ShuffleTensorLinear`.
--
--   **Imports.** It imports the bundles `OAIQ368Chrom002`, `OAIQ368Chrom019`, `OAIQ368Chrom020` and `OAIQ368Chrom021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom023`; the proofs of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom002
import Definitions.Def_OAIQ368Chrom019
import Definitions.Def_OAIQ368Chrom020
import Definitions.Def_OAIQ368Chrom021

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossDifference
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.fourValue_tmul _root_.OAI.ElementaryPositivity.RawShuffle.labeledPolynomial_algebraMap _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_fourValue _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_product _root_.OAI.ElementaryPositivity.RawShuffle.shuffleTensorLinear_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.twoTargetTransfer_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma map_relativeTaylor (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    Polynomial.map (tensorValueAlg d e).toRingHom (relativeTaylor d e f) =
      relativeRaw d e (tensorValue d e f) := by
  induction f using OAI.tensorInductionOn with
  | tmul f g =>
    rw [relativeTaylor_tmul,Polynomial.map_mul,map_taylorS_left,
      Polynomial.map_C,tensorValue_tmul,map_mul,relativeRaw_left,relativeRaw_right]
    congr 1
    change Polynomial.C (tensorValue d e (1 ⊗ₜ[ℚ] g)) = _
    simp
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]

lemma relativeTaylor_crossTensor_monic (d e : I → ℕ) :
    (relativeTaylor d e (crossTensor d e)).Monic := by
  apply Polynomial.monic_of_injective (f := (tensorValueAlg d e).toRingHom) (tensorValue_injective d e)
  rw [map_relativeTaylor,tensorValue_crossTensor]
  exact relativeRaw_crossDifference_monic d e

lemma crossClearing_monic (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    (crossClearing a μ d e).Monic :=
  (relativeTaylor_crossTensor_monic d e).map _

lemma crossClearing_cancel (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : Polynomial (B a μ d ⊗[ℚ] B a μ e)) :
    crossClearing a μ d e * f = 0 ↔ f = 0 :=
  (crossClearing_monic a μ d e).mul_right_eq_zero_iff

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ShuffleTensorLinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tensorShuffle_tensorValue (a : I → I → ℕ) (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    tensorShuffle a (tensorValue d e f) = localizeS (d+e) (shuffleTensorLinear a d e f) := by
  induction f using OAI.tensorInductionOn with
  | tmul f g =>
    rw [tensorValue_tmul,tensorShuffle_decomposable,shuffleTensorLinear_tmul]
    exact (shufflePolynomial_eq a f g).symm
  | add f g hf hg => simp only [map_add,hf,hg]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellVars
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*}

def cellAction (d e : I → ℕ) : CellGroup d e →* Equiv.Perm (CellVars d e) :=
  sumAction (packAction (fun i=>Fin (d i))) (packAction (fun i=>Fin (e i)))

variable [Fintype I] [DecidableEq I]

lemma fourValue_separateFour (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ)
    (hp : ∀ σ, rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ) p = p) :
    fourValue d₁ e₁ d₂ e₂ (separateFour d₁ e₁ d₂ e₂ p) = p := by
  have hh := invariant_separated_span (cellAction d₁ e₁) (cellAction d₂ e₂) p hp
  clear hp
  induction hh using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f,g,hf,hg,rfl⟩ := hp
    rw [separateFour_product,fourValue_tmul,
      tensorValue_separateTensor d₁ e₁ f hf,tensorValue_separateTensor d₂ e₂ g hg]
  | zero => rw [(separateFour d₁ e₁ d₂ e₂).map_zero, (fourValue d₁ e₁ d₂ e₂).map_zero]
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul c f hf ih => simp only [map_smul,ih]

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def cutKernel (a : I → I → ℕ) {d e : I → ℕ} (A : Cut d e) :
    FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ) :=
  algebraMap _ _ (∏ i, ∏ j,cutFactor A i j (a i j)) /
    algebraMap _ _ (cutDenominator A)

lemma tensorShuffle_kernel (a : I → I → ℕ) {d e : I → ℕ}
    (p : MvPolynomial (CellVars d e) ℚ) : tensorShuffle a p =
      ∑ A : Cut d e, algebraMap _ _ (rename (cutSplit A) p) * cutKernel a A := by
  simp only [tensorShuffle,LinearMap.coe_mk,AddHom.coe_mk,map_mul,cutKernel,mul_div_assoc]

noncomputable def doubleTensorShuffle (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ →ₗ[ℚ]
      FractionRing (MvPolynomial (CellVars (d₁+e₁) (d₂+e₂)) ℚ) where
  toFun p := ∑ A : Cut d₁ e₁, ∑ B : Cut d₂ e₂,
    algebraMap _ _ (rename (Sum.map (cutSplit A) (cutSplit B)) p) *
    renameInjFraction Sum.inl Sum.inl_injective (cutKernel a A) *
    renameInjFraction Sum.inr Sum.inr_injective (cutKernel a B)
  map_add' := by
    intro p q
    simp only [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    let : DistribSMul ℚ (FractionRing (MvPolynomial (CellVars (d₁+e₁) (d₂+e₂)) ℚ)) :=
      (inferInstance : Module ℚ (FractionRing (MvPolynomial (CellVars (d₁+e₁) (d₂+e₂)) ℚ))).toDistribMulAction.toDistribSMul
    intro r p
    simp only [map_smul,map_rat_smul,smul_mul_assoc,Finset.smul_sum,RingHom.id_apply]

lemma doubleTensorShuffle_product (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : MvPolynomial (CellVars d₁ e₁) ℚ) (g : MvPolynomial (CellVars d₂ e₂) ℚ) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ (rename Sum.inl f * rename Sum.inr g) =
      renameInjFraction Sum.inl Sum.inl_injective (tensorShuffle a f) *
      renameInjFraction Sum.inr Sum.inr_injective (tensorShuffle a g) := by
  rw [tensorShuffle_kernel,tensorShuffle_kernel]
  simp only [map_sum,map_mul,renameInjFraction_algebraMap,
    Finset.sum_mul,Finset.mul_sum,doubleTensorShuffle,LinearMap.coe_mk,AddHom.coe_mk,
    rename_rename]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  change
    (algebraMap _ _ (rename (Sum.inl ∘ cutSplit A) f) *
      algebraMap _ _ (rename (Sum.inr ∘ cutSplit B) g)) * _ * _ = _
  ring

lemma doubleTensorShuffle_fourValue (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ f) =
      localizeTensor (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ f) := by
  induction f using OAI.tensorInductionOn with
  | tmul f g =>
    rw [fourValue_tmul,doubleTensorShuffle_product,tensorShuffle_tensorValue,
      tensorShuffle_tensorValue]
    simp only [localizeS_apply,
      twoTargetTransfer,TensorProduct.map_tmul,localizeTensor,LinearMap.coe_mk,AddHom.coe_mk,
      tensorValue_tmul,map_mul]
    exact congrArg₂ (· * ·)
      (renameInjFraction_algebraMap Sum.inl Sum.inl_injective _)
      (renameInjFraction_algebraMap Sum.inr Sum.inr_injective _)
  | add f g hf hg =>
    rw [(fourValue d₁ e₁ d₂ e₂).map_add,
      (doubleTensorShuffle a d₁ e₁ d₂ e₂).map_add,
      (twoTargetTransfer a d₁ e₁ d₂ e₂).map_add,
      (localizeTensor (d₁+e₁) (d₂+e₂)).map_add,hf,hg]

lemma doubleTensorShuffle_invariant (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ)
    (hp : ∀ σ, rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ) p = p) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ p =
      localizeTensor (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p) := by
  change _ = localizeTensor _ _ (twoTargetTransfer _ _ _ _ _ (separateFour _ _ _ _ p))
  rw [← doubleTensorShuffle_fourValue, fourValue_separateFour d₁ e₁ d₂ e₂ p hp]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Realization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.cutByShape_snd _root_.OAI.ElementaryPositivity.RawShuffle.cutByShape_symm _root_.OAI.ElementaryPositivity.RawShuffle.embedPackCut_left _root_.OAI.ElementaryPositivity.RawShuffle.embedPackCut_right _root_.OAI.ElementaryPositivity.RawShuffle.labeledPolynomial_algebraMap _root_.OAI.ElementaryPositivity.RawShuffle.mapPackCut_left _root_.OAI.ElementaryPositivity.RawShuffle.mapPackCut_right _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_realization_independent {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (r t : Realization d s) (f : S d) :
    rename (realizationMap r) f.val = rename (realizationMap t) f.val := by
  let σ : ∀ i,Equiv.Perm (Fin (d i)) := fun i => (r i).trans (t i).symm
  have he : realizationMap t ∘ packAction (fun i => Fin (d i)) σ = realizationMap r := by
    funext ⟨i,x⟩
    change (⟨i,↑(t i (σ i x))⟩ : Σi,A i) = ⟨i,↑(r i x)⟩
    simp [σ]
  rw [← he, ← rename_rename, f.property σ]

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma valueAt_independent {d : I → ℕ} {s : ∀ i,Finset (A i)}
    (r t : Realization d s) (f : S d) : valueAt r f = valueAt t f := by
  rw [valueAt,valueAt,rename_realization_independent]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma labeledValue_eq {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) (f : S d) :
    labeledValue f s = valueAt r f := by
  have h : ∀ i,(s i).card = d i := by
    intro i
    simpa using (Fintype.card_congr (r i)).symm
  rw [labeledValue, dite_eq_left h, valueAt_independent _ r]

omit [∀ i,DecidableEq (A i)] in
lemma valueAt_shuffle (a : I → I → ℕ) {d e : I → ℕ}
    (s : ∀ i,Finset (A i)) (r : Realization (d+e) s) (f : S d) (g : S e) :
    valueAt r (shufflePolynomial a f g) =
    renameInjFraction (realizationMap r) (realizationMap_injective r) (rawShuffle a f.val g.val) := by
  rw [← shufflePolynomial_eq]
  exact (renameInjFraction_algebraMap (realizationMap r) (realizationMap_injective r)
    (shufflePolynomial a f g).val).symm

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def leftRealization {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    Realization d (PackConvolution.left (cutRealizationEquiv r t).val) :=
  fun i => (leftEnum t i).trans (PackEnumeration.mapEquiv
    (PackEnumeration.embedding (r i)) (t i).val)

noncomputable def rightRealization {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    Realization e (PackConvolution.right (cutRealizationEquiv r t).val) :=
  fun i => (rightEnum t i).trans (PackEnumeration.mapEquiv
    (PackEnumeration.embedding (r i)) (t i).valᶜ)

omit [Fintype I] [DecidableEq I] in
lemma leftRealization_map {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    realizationMap (leftRealization r t) = realizationMap r ∘ leftInput t := rfl
omit [Fintype I] [DecidableEq I] in
lemma rightRealization_map {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) :
    realizationMap (rightRealization r t) = realizationMap r ∘ rightInput t := rfl

omit [DecidableEq I] in
lemma labeledValue_left {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (f : S d) :
    labeledValue f (PackConvolution.left (cutRealizationEquiv r t).val) =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
        (rename (realizationMap r) (rename (leftInput t) f.val)) := by
  rw [labeledValue_eq (leftRealization r t),valueAt,leftRealization_map,rename_rename]
omit [DecidableEq I] in
lemma labeledValue_right {d e : I → ℕ} {s : ∀ i,Finset (A i)}
    (r : Realization (d+e) s) (t : Cut d e) (g : S e) :
    labeledValue g (PackConvolution.right (cutRealizationEquiv r t).val) =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
        (rename (realizationMap r) (rename (rightInput t) g.val)) := by
  rw [labeledValue_eq (rightRealization r t),valueAt,rightRealization_map,rename_rename]

lemma mapped_cut_kernel (a : I → I → ℕ) {d e : I → ℕ}
    {s : ∀ i,Finset (A i)} (r : Realization (d+e) s) (t : Cut d e) :
    PackConvolution.kernel (pairKernel a)
      (PackConvolution.left (cutRealizationEquiv r t).val)
      (PackConvolution.right (cutRealizationEquiv r t).val) =
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (rename (realizationMap r) (∏ i,∏ j,cutFactor t i j (a i j))) /
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (rename (realizationMap r) (cutDenominator t)) := by
  rw [kernel_formula]
  simp only [cutRealizationEquiv_left,cutRealizationEquiv_right,
    Finset.prod_map,cutFactor,cutDenominator,map_prod,map_pow,diagonal,map_sub,rename_X,pow_one]
  rfl

variable [∀ i,Fintype (A i)]

lemma valueAt_shuffle_sum (a : I → I → ℕ) {d e : I → ℕ}
    {s : ∀ i,Finset (A i)} (r : Realization (d+e) s) (f : S d) (g : S e) :
    valueAt r (shufflePolynomial a f g) =
      ∑ p : SizedCut d s, labeledValue f (PackConvolution.left p.val) *
        labeledValue g (PackConvolution.right p.val) *
          PackConvolution.kernel (pairKernel a)
            (PackConvolution.left p.val) (PackConvolution.right p.val) := by
  classical
  rw [valueAt_shuffle a s r, ← (cutRealizationEquiv r).sum_comp]
  simp only [rawShuffle,map_sum,map_div₀]
  apply Finset.sum_congr rfl
  intro t ht
  rw [labeledValue_left,labeledValue_right,mapped_cut_kernel]
  have hn := renameInjFraction_algebraMap (α := Σi,Fin (d i+e i)) (realizationMap r) (realizationMap_injective r)
    (cutNumerator a t f.val g.val)
  have hd := renameInjFraction_algebraMap (α := Σi,Fin (d i+e i)) (realizationMap r) (realizationMap_injective r)
    (cutDenominator t)
  rw [hn,hd]
  simp only [cutNumerator,map_mul]
  rw [mul_div_assoc]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma cut_card_add {d e : I → ℕ} {s : ∀ i,Finset (A i)} (p : PackConvolution.Cut s)
    (hl : ∀ i,(PackConvolution.left p i).card = d i)
    (hr : ∀ i,(PackConvolution.right p i).card = e i) :
    ∀ i,(s i).card = (d+e) i := by
  intro i
  have h := Finset.card_union_of_disjoint (p i).property.1
  rw [(p i).property.2] at h
  exact h.trans (congrArg₂ (·+·) (hl i) (hr i))

lemma pack_shuffle_sum (a : I → I → ℕ) {d e : I → ℕ}
    (s : ∀ i,Finset (A i)) (f : S d) (g : S e) :
    PackConvolution.shuffle (pairKernel a) (labeledValue f) (labeledValue g) s =
      ∑ p : SizedCut d s, labeledValue f (PackConvolution.left p.val) *
        labeledValue g (PackConvolution.right p.val) *
          PackConvolution.kernel (pairKernel a)
            (PackConvolution.left p.val) (PackConvolution.right p.val) := by
  classical
  unfold PackConvolution.shuffle
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun p : PackConvolution.Cut s => ∀ i,(PackConvolution.left p i).card = d i)]
  suffices hz : (∑ p : {p : PackConvolution.Cut s //
      ¬ ∀ i,(PackConvolution.left p i).card = d i},
      labeledValue f (PackConvolution.left p.val) * labeledValue g (PackConvolution.right p.val) *
      PackConvolution.kernel (pairKernel a)
        (PackConvolution.left p.val) (PackConvolution.right p.val)) = 0 by
    rw [hz,add_zero]
  apply Finset.sum_eq_zero
  intro p hp
  rw [labeledValue,dite_eq_right p.property,zero_mul,zero_mul]

lemma labeledValue_shuffle (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e) :
    labeledValue (A := A) (shufflePolynomial a f g) =
      PackConvolution.shuffle (pairKernel a) (labeledValue f) (labeledValue g) := by
  classical
  funext s
  by_cases hs : ∀ i,(s i).card = (d+e) i
  · rw [labeledValue_eq (defaultRealization hs),valueAt_shuffle_sum,pack_shuffle_sum]
  · rw [labeledValue,dite_eq_right hs,PackConvolution.shuffle]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hl : ∀ i,(PackConvolution.left p i).card = d i
    · have hr : ¬ ∀ i,(PackConvolution.right p i).card = e i := by
        intro hh
        exact hs (cut_card_add p hl hh)
      simp only [labeledValue,dite_eq_right hr,mul_zero,zero_mul]
    · simp only [labeledValue,dite_eq_right hl,zero_mul,zero_mul]

omit [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma labeledValue_injective {d : I → ℕ} {s : ∀ i,Finset (A i)} (r : Realization d s) :
    Function.Injective (fun f : S d => labeledValue f s) := by
  intro f g hh
  apply valueAt_injective r
  simpa only [labeledValue_eq r] using hh

omit [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma labeledValue_cast {d e : I → ℕ} (h : d=e) (f : S d) :
    labeledValue (A := A) (castS h f) = labeledValue f := by
  subst e
  rfl

theorem shufflePolynomial_assoc (a : I → I → ℕ) {d e b : I → ℕ}
    (f : S d) (g : S e) (h : S b) :
    castS (add_assoc d e b) (shufflePolynomial a (shufflePolynomial a f g) h) =
      shufflePolynomial a f (shufflePolynomial a g h) := by
  classical
  let s : ∀ i,Finset (Fin ((d+(e+b)) i)) := fun _ => Finset.univ
  let r : Realization (d+(e+b)) s := defaultRealization (by intro i; simp [s])
  apply labeledValue_injective r
  dsimp only
  rw [labeledValue_cast,labeledValue_shuffle,labeledValue_shuffle,
    labeledValue_shuffle,labeledValue_shuffle]
  exact congrFun (PackConvolution.shuffle_assoc (pairKernel a)
    (labeledValue f) (labeledValue g) (labeledValue h)) s

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SameDen
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.embedPackCut_left _root_.OAI.ElementaryPositivity.RawShuffle.embedPackCut_right _root_.OAI.ElementaryPositivity.RawShuffle.labeledPolynomial_algebraMap _root_.OAI.ElementaryPositivity.RawShuffle.mapPackCut_left _root_.OAI.ElementaryPositivity.RawShuffle.mapPackCut_right _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

omit [∀ i,DecidableEq (A i)] in
lemma kernel_polynomial_ratio (a : I → I → ℕ) (s t : Pack (A:=A)) :
    kernel (pairKernel a) s t =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (arrowNum a s t) /
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen s t) := by
  rw [kernel_formula]
  simp only [arrowNum,sameDen,map_prod,map_pow]

lemma crossKernel_polynomial (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) :
    ∃ N : MvPolynomial (Σi,A i) ℚ,
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
        kernel (pairKernel a) (left q) (right r) *
        kernel (pairKernel a) (left r) (right q) = algebraMap _ _ N := by
  obtain ⟨b,hb⟩ := crossDen_dvd p q r
  refine ⟨b * arrowNum a (left q) (right r) * arrowNum a (left r) (right q),?_⟩
  have hn := crossDen_ne_zero p q r
  have hn₁ : algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left q) (right r)) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne ((mul_ne_zero_iff.mp hn).1)
  have hn₂ : algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left r) (right q)) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne ((mul_ne_zero_iff.mp hn).2)
  rw [kernel_polynomial_ratio,kernel_polynomial_ratio,hb]
  simp only [crossDen,map_mul]
  field_simp

noncomputable def crossKernelPolynomial (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) : MvPolynomial (Σi,A i) ℚ :=
  (crossKernel_polynomial a p q r).choose

lemma crossKernelPolynomial_spec (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
        kernel (pairKernel a) (left q) (right r) *
        kernel (pairKernel a) (left r) (right q) =
      algebraMap _ _ (crossKernelPolynomial a p q r) :=
  (crossKernel_polynomial a p q r).choose_spec

variable [∀ i,Fintype (A i)]

theorem shuffle_grid_cleared (a : I → I → ℕ)
    (f g : Pack (A:=A) → MvPolynomial (Σi,A i) ℚ)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
      PackConvolution.shuffle (pairKernel a)
        (fun t=>algebraMap _ _ (f t)) (fun t=>algebraMap _ _ (g t)) s =
      ∑ q : PackConvolution.Cut (left p), ∑ r : PackConvolution.Cut (right p),
        algebraMap _ _ (f (fun i=>left q i ∪ left r i) *
          g (fun i=>right q i ∪ right r i) * crossKernelPolynomial a p q r) *
          kernel (pairKernel a) (left q) (right q) *
          kernel (pairKernel a) (left r) (right r) := by
  rw [PackConvolution.shuffle_grid _ _ _ p]
  simp only [Finset.mul_sum,map_mul]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [← crossKernelPolynomial_spec]
  ring

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma sum_cut_by_shape {R : Type*} [AddCommMonoid R] (s : Pack (A:=A))
    (F : PackConvolution.Cut s → R) :
    ∑ q, F q = ∑ d : CutShape s,∑ q : SizedCut (fun i=>(d i).val) s,F q.val := by
  rw [← (cutByShape s).symm.sum_comp,Fintype.sum_sigma]
  rfl

lemma sum_grid_by_shape {R : Type*} [AddCommMonoid R] {s : Pack (A:=A)}
    (p : PackConvolution.Cut s)
    (F : PackConvolution.Cut (left p) → PackConvolution.Cut (right p) → R) :
    ∑ q,∑ r,F q r =
      ∑ d : CutShape (left p),∑ e : CutShape (right p),
        ∑ q : SizedCut (fun i=>(d i).val) (left p),
        ∑ r : SizedCut (fun i=>(e i).val) (right p),F q.val r.val := by
  rw [sum_cut_by_shape]
  simp_rw [sum_cut_by_shape (right p)]
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.sum_comm

def shapeComplement {s : Pack (A:=A)} (d : CutShape s) : I → ℕ :=
  fun i=>(s i).card - (d i).val

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma shape_add_complement {s : Pack (A:=A)} (d : CutShape s) :
    (fun i=>(d i).val) + shapeComplement d = (fun i=>(s i).card) := by
  funext i
  exact Nat.add_sub_of_le (Nat.le_of_lt_succ (d i).isLt)

noncomputable def shapeRealization {s : Pack (A:=A)} (d : CutShape s) :
    Realization ((fun i=>(d i).val) + shapeComplement d) s :=
  defaultRealization (fun i=>(congrFun (shape_add_complement d) i).symm)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LabeledPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma labeledPolynomial_eq {d : I → ℕ} {s : Pack (A:=A)} (r : Realization d s) (f : S d) :
    labeledPolynomial f s = rename (realizationMap r) f.val := by
  have h : ∀ i,(s i).card = d i := by
    intro i
    simpa using (Fintype.card_congr (r i)).symm
  rw [labeledPolynomial,dite_eq_left h,rename_realization_independent _ r]

noncomputable def mapRealization (σ : ∀ i,Equiv.Perm (A i)) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) : Realization d (mapPack σ s) :=
  fun i=>(r i).trans (PackEnumeration.mapEquiv (σ i).toEmbedding (s i))

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma mapRealization_map (σ : ∀ i,Equiv.Perm (A i)) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) :
    realizationMap (mapRealization σ r) = packAction A σ ∘ realizationMap r := rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_labeledPolynomial (σ : ∀ i,Equiv.Perm (A i)) {d : I → ℕ}
    (f : S d) (s : Pack (A:=A)) :
    rename (packAction A σ) (labeledPolynomial f s) = labeledPolynomial f (mapPack σ s) := by
  by_cases h : ∀ i,(s i).card = d i
  · rw [labeledPolynomial_eq (defaultRealization h),
      labeledPolynomial_eq (mapRealization σ (defaultRealization h)),mapRealization_map,rename_rename]
  · have hm : ¬ ∀ i,(mapPack σ s i).card = d i := by simpa [mapPack] using h
    simp only [labeledPolynomial,dite_eq_right h,dite_eq_right hm,map_zero]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_sameDen (σ : ∀ i,Equiv.Perm (A i)) (s t : Pack (A:=A)) :
    rename (packAction A σ) (sameDen s t) = sameDen (mapPack σ s) (mapPack σ t) := by
  simp only [sameDen,mapPack,map_prod,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] in
lemma rename_arrowNum (σ : ∀ i,Equiv.Perm (A i)) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    rename (packAction A σ) (arrowNum a s t) = arrowNum a (mapPack σ s) (mapPack σ t) := by
  simp only [arrowNum,mapPack,map_prod,map_pow,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [∀ i,DecidableEq (A i)] in
lemma rename_pack_kernel (σ : ∀ i,Equiv.Perm (A i)) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    renameFraction (packAction A σ) (kernel (pairKernel a) s t) =
      kernel (pairKernel a) (mapPack σ s) (mapPack σ t) := by
  rw [kernel_polynomial_ratio,kernel_polynomial_ratio,map_div₀,
    renameFraction_algebraMap,renameFraction_algebraMap,rename_sameDen,rename_arrowNum]

noncomputable def gridPolynomial (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    MvPolynomial (Σi,A i) ℚ :=
  labeledPolynomial f (fun i=>left q i ∪ left r i) *
    labeledPolynomial g (fun i=>right q i ∪ right r i) * crossKernelPolynomial a p q r

omit [Fintype I] [DecidableEq I] in
lemma mapPack_union (σ : ∀ i,Equiv.Perm (A i)) (s t : Pack (A:=A)) :
    mapPack σ (fun i=>s i ∪ t i) = fun i=>mapPack σ s i ∪ mapPack σ t i := by
  funext i
  exact Finset.map_union _ _

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_labeledPolynomial (φ : ∀ i,A i ↪ B i) {d : I → ℕ}
    (f : S d) (s : Pack (A:=A)) :
    rename (packEmbedding φ) (labeledPolynomial f s) = labeledPolynomial f (embedPack φ s) := by
  by_cases h : ∀ i,(s i).card = d i
  · rw [labeledPolynomial_eq (defaultRealization h),
      labeledPolynomial_eq (embedRealization φ (defaultRealization h)),embedRealization_map,rename_rename]
  · have hm : ¬ ∀ i,(embedPack φ s i).card = d i := by simpa [embedPack] using h
    simp only [labeledPolynomial,dite_eq_right h,dite_eq_right hm,map_zero]

omit [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_sameDen (φ : ∀ i,A i ↪ B i) (s t : Pack (A:=A)) :
    rename (packEmbedding φ) (sameDen s t) = sameDen (embedPack φ s) (embedPack φ t) := by
  simp only [sameDen,embedPack,map_prod,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_arrowNum (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    rename (packEmbedding φ) (arrowNum a s t) = arrowNum a (embedPack φ s) (embedPack φ t) := by
  simp only [arrowNum,embedPack,map_prod,map_pow,Finset.prod_map,diagonal,map_sub,rename_X]
  rfl

omit [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embed_pack_kernel (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ) (s t : Pack (A:=A)) :
    renameInjFraction (packEmbedding φ) (packEmbedding φ).injective (kernel (pairKernel a) s t) =
      kernel (pairKernel a) (embedPack φ s) (embedPack φ t) := by
  rw [kernel_polynomial_ratio,kernel_polynomial_ratio,map_div₀,
    renameInjFraction_algebraMap,renameInjFraction_algebraMap,embed_sameDen,embed_arrowNum]

lemma embed_crossKernelPolynomial (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    rename (packEmbedding φ) (crossKernelPolynomial a p q r) =
      crossKernelPolynomial a (embedPackCut φ p) (embedPackCut φ q) (embedPackCut φ r) := by
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,B i) ℚ))
  rw [← renameInjFraction_algebraMap (packEmbedding φ) (packEmbedding φ).injective,← crossKernelPolynomial_spec,
    map_mul,map_mul,renameInjFraction_algebraMap,embed_sameDen,
    embed_pack_kernel,embed_pack_kernel]
  exact crossKernelPolynomial_spec a (embedPackCut φ p) (embedPackCut φ q) (embedPackCut φ r)

lemma embed_gridPolynomial (φ : ∀ i,A i ↪ B i) (a : I → I → ℕ)
    {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p)) :
    rename (packEmbedding φ) (gridPolynomial a f g p q r) =
      gridPolynomial a f g (embedPackCut φ p) (embedPackCut φ q) (embedPackCut φ r) := by
  simp only [gridPolynomial,map_mul,embed_labeledPolynomial,embed_crossKernelPolynomial,
    embedPack_union,embedPackCut_left,embedPackCut_right]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SumPackCut
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
  [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

noncomputable def canonicalGridPolynomial (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (Σi,FourPacks d₁ e₁ d₂ e₂ i) ℚ :=
  gridPolynomial a f g (canonicalGridCut d₁ e₁ d₂ e₂)
    (canonicalLeftCut d₁ e₁ d₂ e₂) (canonicalRightCut d₁ e₁ d₂ e₂)

def fourPackAction (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) (i : I) :
    Equiv.Perm (FourPacks d₁ e₁ d₂ e₂ i) :=
  Equiv.sumCongr (Equiv.sumCongr (σ.1.1 i) (σ.1.2 i))
    (Equiv.sumCongr (σ.2.1 i) (σ.2.2 i))

lemma gridPolynomial_stabilized {C : I → Type*} [∀ i,Fintype (C i)] [∀ i,DecidableEq (C i)]
    (σ : ∀ i,Equiv.Perm (C i)) (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=C)} (p : PackConvolution.Cut s)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p))
    (hp₁ : mapPack σ (left p) = left p) (hp₂ : mapPack σ (right p) = right p)
    (hq₁ : mapPack σ (left q) = left q) (hq₂ : mapPack σ (right q) = right q)
    (hr₁ : mapPack σ (left r) = left r) (hr₂ : mapPack σ (right r) = right r) :
    rename (packAction C σ) (gridPolynomial a f g p q r) = gridPolynomial a f g p q r := by
  have hc : rename (packAction C σ) (crossKernelPolynomial a p q r) =
      crossKernelPolynomial a p q r := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,C i) ℚ))
    rw [← renameFraction_algebraMap (packAction C σ),← crossKernelPolynomial_spec,
      map_mul,map_mul,renameFraction_algebraMap,rename_sameDen,
      rename_pack_kernel,rename_pack_kernel,hp₁,hp₂,hq₁,hq₂,hr₁,hr₂]
  simp only [gridPolynomial,map_mul,rename_labeledPolynomial,mapPack_union,hq₁,hq₂,hr₁,hr₂,hc]

lemma canonicalGridPolynomial_invariant (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) :
    rename (packAction (FourPacks d₁ e₁ d₂ e₂) (fourPackAction d₁ e₁ d₂ e₂ σ))
      (canonicalGridPolynomial a f g d₁ e₁ d₂ e₂) =
      canonicalGridPolynomial a f g d₁ e₁ d₂ e₂ := by
  apply gridPolynomial_stabilized
  all_goals
    funext i
    ext x
    rcases x with (x|x) <;> rcases x with (x|x) <;>
      simp [mapPack,canonicalGridCut,canonicalLeftCut,canonicalRightCut,
        sumPackCut,left,right,embedPackCut,fourPackAction,Finset.mem_map,Equiv.sumCongr]

def fourPackEquiv (d₁ e₁ d₂ e₂ : I → ℕ) :
    (Σi,FourPacks d₁ e₁ d₂ e₂ i) ≃ (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) where
  toFun
    | ⟨i,Sum.inl (Sum.inl x)⟩ => Sum.inl (Sum.inl ⟨i,x⟩)
    | ⟨i,Sum.inl (Sum.inr x)⟩ => Sum.inl (Sum.inr ⟨i,x⟩)
    | ⟨i,Sum.inr (Sum.inl x)⟩ => Sum.inr (Sum.inl ⟨i,x⟩)
    | ⟨i,Sum.inr (Sum.inr x)⟩ => Sum.inr (Sum.inr ⟨i,x⟩)
  invFun
    | Sum.inl (Sum.inl ⟨i,x⟩) => ⟨i,Sum.inl (Sum.inl x)⟩
    | Sum.inl (Sum.inr ⟨i,x⟩) => ⟨i,Sum.inl (Sum.inr x)⟩
    | Sum.inr (Sum.inl ⟨i,x⟩) => ⟨i,Sum.inr (Sum.inl x)⟩
    | Sum.inr (Sum.inr ⟨i,x⟩) => ⟨i,Sum.inr (Sum.inr x)⟩
  left_inv := by rintro ⟨i,((x|x)|(x|x))⟩ <;> rfl
  right_inv := by rintro ((⟨i,x⟩|⟨i,x⟩)|(⟨i,x⟩|⟨i,x⟩)) <;> rfl

noncomputable def fourGridPolynomial (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rename (fourPackEquiv d₁ e₁ d₂ e₂) (canonicalGridPolynomial a f g d₁ e₁ d₂ e₂)

lemma fourGridPolynomial_invariant (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) :
    rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ)
      (fourGridPolynomial a f g d₁ e₁ d₂ e₂) = fourGridPolynomial a f g d₁ e₁ d₂ e₂ := by
  have he : (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ) ∘
      fourPackEquiv d₁ e₁ d₂ e₂ = fourPackEquiv d₁ e₁ d₂ e₂ ∘
        packAction (FourPacks d₁ e₁ d₂ e₂) (fourPackAction d₁ e₁ d₂ e₂ σ) := by
    funext z
    rcases z with ⟨i,z⟩
    rcases z with (x|x) <;> rcases x with (x|x) <;> rfl
  unfold fourGridPolynomial
  rw [rename_rename,he,← rename_rename,canonicalGridPolynomial_invariant]

lemma fourGridPolynomial_transfer (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂) =
      localizeTensor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)) :=
  doubleTensorShuffle_invariant a d₁ e₁ d₂ e₂ _
    (fourGridPolynomial_invariant a f g d₁ e₁ d₂ e₂)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

lemma gridPolynomial_congr (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {s t : Pack (A:=A)} (p : PackConvolution.Cut s) (p' : PackConvolution.Cut t)
    (q : PackConvolution.Cut (left p)) (r : PackConvolution.Cut (right p))
    (q' : PackConvolution.Cut (left p')) (r' : PackConvolution.Cut (right p'))
    (hp₁ : left p = left p') (hp₂ : right p = right p')
    (hq₁ : left q = left q') (hq₂ : right q = right q')
    (hr₁ : left r = left r') (hr₂ : right r = right r') :
    gridPolynomial a f g p q r = gridPolynomial a f g p' q' r' := by
  have hc : crossKernelPolynomial a p q r = crossKernelPolynomial a p' q' r' := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,A i) ℚ))
    rw [← crossKernelPolynomial_spec,← crossKernelPolynomial_spec]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
      (congrArg (algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)))
        (congrArg₂ sameDen hp₁ hp₂))
      (congrArg₂ (kernel (pairKernel a)) hq₁ hr₂))
      (congrArg₂ (kernel (pairKernel a)) hr₁ hq₂)
  simp only [gridPolynomial,hq₁,hq₂,hr₁,hr₂,hc]

noncomputable def gridEmbedding {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) (i : I) :
    FourPacks d₁ e₁ d₂ e₂ i ↪ A i where
  toFun := Sum.elim (fun x=>↑(R i (packSplit u i x))) (fun x=>↑(T i (packSplit v i x)))
  inj' := by
    rintro (x|x) (y|y) h
    · congr 1
      exact (packSplit u i).injective ((R i).injective (Subtype.ext h))
    · change (R i (packSplit u i x)).val = (T i (packSplit v i y)).val at h
      exact (Finset.disjoint_left.mp (p i).property.1
        (R i (packSplit u i x)).property (h.symm ▸ (T i (packSplit v i y)).property)).elim
    · change (T i (packSplit v i x)).val = (R i (packSplit u i y)).val at h
      exact (Finset.disjoint_left.mp (p i).property.1
        (R i (packSplit u i y)).property (h ▸ (T i (packSplit v i x)).property)).elim
    · congr 1
      exact (packSplit v i).injective ((T i).injective (Subtype.ext h))

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_outer_left {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (left (canonicalGridCut d₁ e₁ d₂ e₂)) = left p := by
  funext i
  change Finset.map _ (Finset.univ.map Function.Embedding.inl) = _
  rw [Finset.map_map]
  change Finset.univ.map ((packSplit u i).toEmbedding.trans (PackEnumeration.embedding (R i))) = _
  rw [← Finset.map_map,Finset.map_univ_equiv,PackEnumeration.map_univ]

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_outer_right {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (right (canonicalGridCut d₁ e₁ d₂ e₂)) = right p := by
  funext i
  change Finset.map _ (Finset.univ.map Function.Embedding.inr) = _
  rw [Finset.map_map]
  change Finset.univ.map ((packSplit v i).toEmbedding.trans (PackEnumeration.embedding (T i))) = _
  rw [← Finset.map_map,Finset.map_univ_equiv,PackEnumeration.map_univ]

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₁ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (left (canonicalLeftCut d₁ e₁ d₂ e₂)) =
      left (cutRealizationEquiv R u).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inl).map Function.Embedding.inl) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (leftEnum u i)).trans
    (PackEnumeration.embedding (R i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₂ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (right (canonicalLeftCut d₁ e₁ d₂ e₂)) =
      right (cutRealizationEquiv R u).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inr).map Function.Embedding.inl) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (rightEnum u i)).trans
    (PackEnumeration.embedding (R i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₃ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (left (canonicalRightCut d₁ e₁ d₂ e₂)) =
      left (cutRealizationEquiv T v).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inl).map Function.Embedding.inr) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (leftEnum v i)).trans
    (PackEnumeration.embedding (T i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_cell₄ {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    embedPack (gridEmbedding p R T u v) (right (canonicalRightCut d₁ e₁ d₂ e₂)) =
      right (cutRealizationEquiv T v).val := by
  funext i
  change Finset.map _ ((Finset.univ.map Function.Embedding.inr).map Function.Embedding.inr) = _
  rw [Finset.map_map,Finset.map_map]
  change Finset.univ.map ((PackEnumeration.embedding (rightEnum v i)).trans
    (PackEnumeration.embedding (T i))) = _
  rw [← Finset.map_map,PackEnumeration.map_univ]
  rfl

lemma gridPolynomial_realization (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    rename (packEmbedding (gridEmbedding p R T u v)) (canonicalGridPolynomial a f g d₁ e₁ d₂ e₂) =
      gridPolynomial a f g p (cutRealizationEquiv R u).val (cutRealizationEquiv T v).val := by
  rw [canonicalGridPolynomial,embed_gridPolynomial]
  apply gridPolynomial_congr
  · exact gridEmbedding_outer_left p R T u v
  · exact gridEmbedding_outer_right p R T u v
  · exact gridEmbedding_cell₁ p R T u v
  · exact gridEmbedding_cell₂ p R T u v
  · exact gridEmbedding_cell₃ p R T u v
  · exact gridEmbedding_cell₄ p R T u v

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TargetEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_square {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    targetEmbedding p R T ∘ Sum.map (cutSplit u) (cutSplit v) ∘ fourPackEquiv d₁ e₁ d₂ e₂ =
      packEmbedding (gridEmbedding p R T u v) := by
  funext z
  rcases z with ⟨i,z⟩
  rcases z with (x|x) <;> rcases x with (x|x) <;> rfl

lemma gridPolynomial_four_realization (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    rename (targetEmbedding p R T) (rename (Sum.map (cutSplit u) (cutSplit v))
      (fourGridPolynomial a f g d₁ e₁ d₂ e₂)) =
      gridPolynomial a f g p (cutRealizationEquiv R u).val (cutRealizationEquiv T v).val := by
  simp only [fourGridPolynomial,rename_rename]
  change rename (targetEmbedding p R T ∘ Sum.map (cutSplit u) (cutSplit v) ∘
    fourPackEquiv d₁ e₁ d₂ e₂) _ = _
  rw [gridEmbedding_square,gridPolynomial_realization]

omit [Fintype I] [DecidableEq I] in
lemma targetEmbedding_algebraMap {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (P : MvPolynomial (CellVars d e) ℚ) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (algebraMap _ (FractionRing (MvPolynomial (CellVars d e) ℚ)) P) =
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (rename (targetEmbedding p R T) P) :=
  renameInjFraction_algebraMap (targetEmbedding p R T) (targetEmbedding p R T).injective P

lemma targetEmbedding_left_kernel (a : I → I → ℕ)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction Sum.inl Sum.inl_injective (cutKernel a u)) =
      kernel (pairKernel a) (left (cutRealizationEquiv R u).val)
        (right (cutRealizationEquiv R u).val) := by
  have hpoly (P : MvPolynomial (Σ i, Fin (d₁ i + e₁ i)) ℚ) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction (Sum.inl : (Σ i, Fin (d₁ i + e₁ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inl_injective
        (algebraMap _ (FractionRing (MvPolynomial (Σ i, Fin (d₁ i + e₁ i)) ℚ)) P)) =
    algebraMap _ (FractionRing (MvPolynomial (Σ i,A i) ℚ)) (rename (realizationMap R) P) := by
    have h₁ := renameInjFraction_algebraMap
      (Sum.inl : (Σ i, Fin (d₁ i + e₁ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inl_injective P
    have h₂ := renameInjFraction_algebraMap (targetEmbedding p R T) (targetEmbedding p R T).injective
      (rename (Sum.inl : (Σ i, Fin (d₁ i + e₁ i)) → CellVars (d₁+e₁) (d₂+e₂)) P)
    calc
      _ = _ := congrArg (renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective) h₁
      _ = _ := h₂
      _ = _ := by rw [rename_rename]; rfl
  simp only [cutKernel,map_div₀,hpoly]
  rw [mapped_cut_kernel]

lemma targetEmbedding_right_kernel (a : I → I → ℕ)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (v : Cut d₂ e₂) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction Sum.inr Sum.inr_injective (cutKernel a v)) =
      kernel (pairKernel a) (left (cutRealizationEquiv T v).val)
        (right (cutRealizationEquiv T v).val) := by
  have hpoly (P : MvPolynomial (Σ i, Fin (d₂ i + e₂ i)) ℚ) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction (Sum.inr : (Σ i, Fin (d₂ i + e₂ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inr_injective
        (algebraMap _ (FractionRing (MvPolynomial (Σ i, Fin (d₂ i + e₂ i)) ℚ)) P)) =
    algebraMap _ (FractionRing (MvPolynomial (Σ i,A i) ℚ)) (rename (realizationMap T) P) := by
    have h₁ := renameInjFraction_algebraMap
      (Sum.inr : (Σ i, Fin (d₂ i + e₂ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inr_injective P
    have h₂ := targetEmbedding_algebraMap p R T
      (rename (Sum.inr : (Σ i, Fin (d₂ i + e₂ i)) → CellVars (d₁+e₁) (d₂+e₂)) P)
    calc
      _ = _ := congrArg (renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective) h₁
      _ = _ := h₂
      _ = _ := by rw [rename_rename]; rfl
  simp only [cutKernel,map_div₀,hpoly]
  rw [mapped_cut_kernel]

lemma grid_shape_transfer [∀ i,Fintype (A i)] (a : I → I → ℕ)
    {d e : I → ℕ} (f : S d) (g : S e)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) :
    (∑ q : SizedCut d₁ (left p),∑ r : SizedCut d₂ (right p),
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (gridPolynomial a f g p q.val r.val) *
        kernel (pairKernel a) (left q.val) (right q.val) *
        kernel (pairKernel a) (left r.val) (right r.val)) =
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (localizeTensor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))) := by
  rw [← fourGridPolynomial_transfer,doubleTensorShuffle]
  simp only [LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_mul,
    targetEmbedding_left_kernel,targetEmbedding_right_kernel]
  rw [← (cutRealizationEquiv R).sum_comp]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← (cutRealizationEquiv T).sum_comp]
  apply Finset.sum_congr rfl
  intro v hv
  apply congrArg (fun z => z *
    kernel (pairKernel a) (left (cutRealizationEquiv R u).val) (right (cutRealizationEquiv R u).val) *
    kernel (pairKernel a) (left (cutRealizationEquiv T v).val) (right (cutRealizationEquiv T v).val))
  symm
  calc
    _ = _ := renameInjFraction_algebraMap (targetEmbedding p R T) (targetEmbedding p R T).injective _
    _ = _ := congrArg (algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)))
      (gridPolynomial_four_realization a f g p R T u v)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

omit [DecidableEq I] in
lemma targetValueAt_tmul {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (f : S d) (g : S e) :
    targetValueAt p R T (f ⊗ₜ[ℚ] g) = labeledValue f (left p) * labeledValue g (right p) := by
  rw [labeledValue_eq R,labeledValue_eq T]
  simp only [targetValueAt_apply,LinearMap.coe_mk,AddHom.coe_mk,localizeTensor,tensorValue_tmul,
    targetEmbedding_algebraMap,map_mul,rename_rename,valueAt]
  rfl

omit [DecidableEq I] in
lemma targetValueAt_independent {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R R' : Realization d (left p)) (T T' : Realization e (right p)) :
    targetValueAt p R T = targetValueAt p R' T' := by
  apply AddMonoidHom.ext
  intro t
  induction t using OAI.tensorInductionOn with
  | tmul f g => rw [targetValueAt_tmul,targetValueAt_tmul]
  | add f g hf hg => simp only [map_add,hf,hg]

omit [DecidableEq I] in
lemma targetValueAt_cast {d e d' e' : I → ℕ} (h : d=d') (k : e=e') {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (R' : Realization d' (left p))
    (T : Realization e (right p)) (T' : Realization e' (right p)) (t : S d ⊗[ℚ] S e) :
    targetValueAt p R' T' (castTensor h k t) = targetValueAt p R T t := by
  subst d'
  subst e'
  rw [targetValueAt_independent p R' R T' T]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridShapeTensor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor
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
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma targetEmbedding_realization {d e : I → ℕ} {s : Pack (A:=A)}
    (R : Realization (d+e) s) (u : Cut d e) :
    targetEmbedding (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u) =
      (cutSplit u).toEmbedding.trans
        (⟨realizationMap R, realizationMap_injective R⟩ : (Σi,Fin ((d+e) i)) ↪ (Σi,A i)) := by
  apply Function.Embedding.ext
  intro z
  rcases z with x|x <;> rfl

omit [∀ i,Fintype (A i)] in
lemma targetValueAt_restrictTensor {d e : I → ℕ} {s : Pack (A:=A)}
    (R : Realization (d+e) s) (u : Cut d e) (f : S (d+e)) :
    targetValueAt (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u)
      (restrictTensor u f) = labeledValue f s := by
  rw [labeledValue_eq R]
  change renameInjFraction
    (targetEmbedding (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u))
    (targetEmbedding (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u)).injective
    (algebraMap (MvPolynomial (CellVars d e) ℚ) (FractionRing (MvPolynomial (CellVars d e) ℚ))
      (tensorValue d e (restrictTensor u f))) = _
  rw [tensorValue_restrictTensor,targetEmbedding_algebraMap]
  simp only [rename_rename,targetEmbedding_realization,Function.Embedding.coe_trans,
    Equiv.coe_toEmbedding]
  change algebraMap _ _ (rename ((realizationMap R ∘ cutSplit u) ∘ (cutSplit u).symm) f.val) = _
  have hfun : (realizationMap R ∘ cutSplit u) ∘ (cutSplit u).symm = realizationMap R := by
    funext x
    simp
  rw [hfun]
  rfl

noncomputable def gridShapeTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) : S α ⊗[ℚ] S β :=
  castTensor ((shape_add_complement u).trans (realization_card R))
    ((shape_add_complement v).trans (realization_card T))
    (cellTransfer a (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)
      (fourGridPolynomial a f g (fun i=>(u i).val) (shapeComplement u)
        (fun i=>(v i).val) (shapeComplement v)))

lemma targetValueAt_gridShapeTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) :
    targetValueAt p R T (gridShapeTensor a f g p R T u v) =
      ∑ q : SizedCut (fun i=>(u i).val) (left p),
      ∑ r : SizedCut (fun i=>(v i).val) (right p),
        algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (gridPolynomial a f g p q.val r.val) *
          kernel (pairKernel a) (left q.val) (right q.val) *
          kernel (pairKernel a) (left r.val) (right r.val) := by
  rw [gridShapeTensor,targetValueAt_cast _ _ p (shapeRealization u) R (shapeRealization v) T]
  exact (grid_shape_transfer a f g p (shapeRealization u) (shapeRealization v)).symm

noncomputable def gridTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) : S α ⊗[ℚ] S β :=
  ∑ u : CutShape (left p),∑ v : CutShape (right p),gridShapeTensor a f g p R T u v

lemma targetValueAt_gridTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) :
    targetValueAt p R T (gridTensor a f g p R T) =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
        labeledValue (shufflePolynomial a f g) s := by
  rw [labeledValue_shuffle]
  have hf : labeledValue (A:=A) f = fun t=>algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (labeledPolynomial f t) := by
    funext t; exact (labeledPolynomial_algebraMap f t).symm
  have hg : labeledValue (A:=A) g = fun t=>algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (labeledPolynomial g t) := by
    funext t; exact (labeledPolynomial_algebraMap g t).symm
  rw [hf,hg,shuffle_grid_cleared, sum_grid_by_shape p]
  simp only [gridTensor,map_sum,targetValueAt_gridShapeTensor,gridPolynomial]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CanonicalCard
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma fourGridPolynomial_zero_of_source_mismatch (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) (hd : d₁+d₂ ≠ d) :
    fourGridPolynomial a f g d₁ e₁ d₂ e₂ = 0 := by
  have hf : labeledPolynomial f (fun i=>left (canonicalLeftCut d₁ e₁ d₂ e₂) i ∪
      left (canonicalRightCut d₁ e₁ d₂ e₂) i) = 0 := by
    apply dite_eq_right
    intro h
    apply hd
    funext i
    exact (canonical_source_card d₁ e₁ d₂ e₂ i).symm.trans (h i)
  simp [fourGridPolynomial,canonicalGridPolynomial,gridPolynomial,hf]

omit [∀ i,Fintype (A i)] in
lemma quotient_gridShapeTensor_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hα : slope c η α = slope c η β) (hμ : slope c η d > slope c η α) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) = 0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val) + (fun i=>(v i).val) = d
  · apply quotient_cellTransfer_zero
    apply destabilized_target c η hc
    · rw [(shape_add_complement u).trans (realization_card R),
        (shape_add_complement v).trans (realization_card T)]
      exact hα
    · rw [hsum]; exact hd
    · rw [hsum,(shape_add_complement u).trans (realization_card R)]
      exact hμ
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [∀ i,Fintype (A i)] in
lemma quotient_gridTensor_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) (hd : d≠0)
    (hα : slope c η α = slope c η β) (hμ : slope c η d > slope c η α) :
    quotientTensor a (slope c η) α β (gridTensor a f g p R T) = 0 := by
  simp only [gridTensor,map_sum]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  exact quotient_gridShapeTensor_zero a c η hc f g p R T u v hd hα hμ

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [DecidableEq I] [∀ i,Fintype (A i)] in
lemma sameDen_realization {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    sameDen (left p) (right p) =
    ∏ i,∏ x : Fin (d i), ∏ y : Fin (e i),
      (X (realizationMap T ⟨i,y⟩) - X (realizationMap R ⟨i,x⟩)) := by
  unfold sameDen
  apply Finset.prod_congr rfl
  intro i hi
  rw [← PackEnumeration.map_univ (R i),← PackEnumeration.map_univ (T i)]
  simp only [Finset.prod_map,diagonal,realizationMap]
  rfl

omit [DecidableEq I] [∀ i,Fintype (A i)] in
lemma targetEmbedding_crossDifference {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    rename (targetEmbedding p R T) (crossDifference d e) =
      C (crossSign d e) * sameDen (left p) (right p) := by
  rw [sameDen_realization p R T]
  simp only [crossDifference,map_prod,map_sub,rename_X,crossSign,map_neg,map_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x hx
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro y hy
  change X (realizationMap R ⟨i,x⟩) - X (realizationMap T ⟨i,y⟩) =
    -1 * (X (realizationMap T ⟨i,y⟩) - X (realizationMap R ⟨i,x⟩))
  ring

omit [∀ i,Fintype (A i)] in
lemma targetValueAt_crossTensor {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    targetValueAt p R T (crossTensor d e) = crossSign d e •
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) := by
  change renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
    (algebraMap (MvPolynomial (CellVars d e) ℚ) (FractionRing (MvPolynomial (CellVars d e) ℚ))
      (tensorValue d e (crossTensor d e))) = _
  rw [tensorValue_crossTensor]
  have hh := targetEmbedding_algebraMap p R T (crossDifference d e)
  calc
    _ = _ := hh
    _ = _ := by
      rw [targetEmbedding_crossDifference, ← smul_eq_C_mul]
      exact map_rat_smul (algebraMap (MvPolynomial (Σi,A i) ℚ)
        (FractionRing (MvPolynomial (Σi,A i) ℚ))).toAddMonoidHom _ _

lemma cleared_restrictTensor (a : I → I → ℕ) {d e α β : I → ℕ} (h : d+e=α+β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) (u : Cut α β) :
    crossTensor α β * restrictTensor u (castS h (shufflePolynomial a f g)) =
      crossSign α β • gridTensor a f g (cutRealizationEquiv R u).val
        (leftRealization R u) (rightRealization R u) := by
  apply targetValueAt_injective (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u)
  rw [targetValueAt_mul,targetValueAt_crossTensor,targetValueAt_restrictTensor,
    targetValueAt_smul,targetValueAt_gridTensor,labeledValue_cast]
  exact smul_mul_assoc _ _ _

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma quotient_crossTensor_cancel (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (t : S d ⊗[ℚ] S e) (h : quotientTensor a μ d e (crossTensor d e * t) = 0) :
    quotientTensor a μ d e t = 0 := by
  have ht := quotient_relativeTaylor_zero a μ d e (crossTensor d e * t) h
  rw [map_mul,Polynomial.map_mul] at ht
  have hz : Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e t) = 0 :=
    (crossClearing_cancel a μ d e _).mp ht
  have he := congrArg (fun p : Polynomial (B a μ d ⊗[ℚ] B a μ e) => p.eval 0) hz
  rw [← show algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e) 0 = 0 from map_zero _] at he
  rw [eval_map_rat,relativeTaylor_eval] at he
  have htr : TensorProduct.map (translationS d 0) (LinearMap.id : S e →ₗ[ℚ] S e) t = t := by
    clear h ht hz he
    induction t using OAI.tensorInductionOn with
    | tmul f g => simp [translationS]
    | add f g hf hg => simp only [map_add,hf,hg]
  simpa only [htr,Polynomial.eval_zero,Polynomial.coeff_zero] using he

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictionB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem restrict_destabilizing_shuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (u : Cut α β)
    (hd : d≠0) (hα : slope c η α = slope c η β)
    (hμ : slope c η d > slope c η (α+β)) :
    quotientTensor a (slope c η) α β
      (restrictTensor u (dimensionCast h (shufflePolynomial a f g))) = 0 := by
  rw [dimensionCast_eq_castS]
  apply quotient_crossTensor_cancel
  let s : Pack (A:=fun i=>Fin ((α+β) i)) := fun _=>Finset.univ
  let R : Realization (α+β) s := defaultRealization (by intro i; simp [s])
  rw [cleared_restrictTensor a h f g R u, map_smul]
  rw [quotient_gridTensor_zero a c η hc f g _ _ _ hd hα]
  · simp
  · rwa [slope_add_same c η hc hα] at hμ

theorem restriction_kills_destabilizingSpace (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) {d e : I → ℕ} (hs : slope c η d = slope c η e)
    (u : Cut d e) {f : S (d+e)} (hf : f ∈ destabilizingSpace a (slope c η) (d+e)) :
    quotientTensor a (slope c η) d e (restrictTensor u f) = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α,β,h,F,G,hα,hβ,hμ,rfl⟩ := hf
    exact restrict_destabilizing_shuffle a c η hc h F G u hα hs hμ
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg,add_zero]
  | smul r f hf ih => simp only [map_smul,ih,smul_zero]

noncomputable def restrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) :
    B a (slope c η) (d+e) →ₐ[ℚ] B a (slope c η) d ⊗[ℚ] B a (slope c η) e :=
  Ideal.Quotient.liftₐ (destabilizingIdeal a (slope c η) (d+e))
    ((quotientTensor a (slope c η) d e).comp (restrictTensorAlg u))
    (by intro f hf; exact restriction_kills_destabilizingSpace a c η hc hs u hf)

@[simp] lemma restrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) (f : S (d+e)) :
    restrictionB a c η hc hs u (quotientAlg a (slope c η) (d+e) f) =
      quotientTensor a (slope c η) d e (restrictTensor u f) := rfl

noncomputable def restrictionRelativeB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) :
    B a (slope c η) (d+e) →ₐ[ℚ] Polynomial (B a (slope c η) d ⊗[ℚ] B a (slope c η) e) :=
  (relativeTaylorB a (slope c η) d e).comp (restrictionB a c η hc hs u)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

@[reducible] def OnSlope (c η : I → ℝ) (θ : ℝ) : SplitTree I → Prop
  | .leaf d => d ≠ 0 ∧ slope c η d = θ
  | .node l r => l.OnSlope c η θ ∧ r.OnSlope c η θ

omit [DecidableEq I] in
lemma slope_dim (c η : I → ℝ) (hc : ∀ i,0 < c i) {θ : ℝ} {T : SplitTree I}
    (h : T.OnSlope c η θ) : slope c η T.dim = θ := by
  induction T with
  | leaf d => exact h.2
  | node l r ihl ihr =>
    have hl := ihl h.1
    have hr := ihr h.2
    exact (slope_add_same c η hc (hl.trans hr.symm)).trans hl

@[reducible] noncomputable def tensor (A : (I → ℕ) → CommAlgCat.{u} ℚ) : SplitTree I → CommAlgCat.{u} ℚ
  | .leaf d => A d
  | .node l r => CommAlgCat.of ℚ (tensor A l ⊗[ℚ] tensor A r)

noncomputable def quotientFamily (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) : CommAlgCat.{u} ℚ :=
  CommAlgCat.of ℚ (B a μ d)

noncomputable def restrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) : (T : SplitTree I) → T.OnSlope c η θ →
      B a (slope c η) T.dim →ₐ[ℚ] tensor (quotientFamily a (slope c η)) T
  | .leaf d, _ => AlgHom.id ℚ (B a (slope c η) d)
  | .node l r, h =>
    (Algebra.TensorProduct.map (restrictionB a c η hc θ l h.1)
      (restrictionB a c η hc θ r h.2)).comp
        (RawShuffle.restrictionB a c η hc
          ((slope_dim c η hc h.1).trans (slope_dim c η hc h.2).symm)
          (firstCut l.dim r.dim))

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ComponentB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def componentB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) : B a μ d →ₗ[ℚ] B a μ d :=
  (destabilizingSpace a μ d).mapQ (destabilizingSpace a μ d) (componentS d k)
    (fun f hf=>componentS_destabilizing_mem a μ d k f hf)

@[simp] lemma componentB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : S d) :
    componentB a μ d k ((destabilizingSpace a μ d).mkQ f) =
      (destabilizingSpace a μ d).mkQ (componentS d k f) := rfl

omit [Fintype I] [DecidableEq I] in
lemma componentS_componentS (d : I → ℕ) (k l : ℤ) (f : S d) :
    componentS d k (componentS d l f) = if k=l then componentS d l f else 0 :=
  componentS_of_homogeneous _ _ (componentS_homogeneous _ _ _) _

lemma componentB_componentB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k l : ℤ) (f : B a μ d) :
    componentB a μ d k (componentB a μ d l f) =
      if k=l then componentB a μ d l f else 0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (destabilizingSpace a μ d).mkQ (componentS d k (componentS d l f)) =
      if k=l then (destabilizingSpace a μ d).mkQ (componentS d l f) else 0
    rw [componentS_componentS]
    split_ifs <;> simp

@[simp] lemma componentB_idempotent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : B a μ d) :
    componentB a μ d k (componentB a μ d k f) = componentB a μ d k f := by
  rw [componentB_componentB,ite_eq_left rfl]

end ElementaryPositivity.RawShuffle
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma dimensionCast_trans {d e b : I → ℕ} (h : d=e) (j : e=b) (f : S d) :
    dimensionCast j (dimensionCast h f) = dimensionCast (h.trans j) f := by
  subst e; subst b; rfl

lemma shuffle_assoc_cast (a : I → I → ℕ) {d e b : I → ℕ}
    (f : S d) (g : S e) (h : S b) :
    dimensionCast (add_assoc d e b) (shufflePolynomial a (shufflePolynomial a f g) h) =
      shufflePolynomial a f (shufflePolynomial a g h) := by
  rw [dimensionCast_eq_castS]
  exact shufflePolynomial_assoc a f g h

lemma shuffle_assoc_cast_symm (a : I → I → ℕ) {d e b : I → ℕ}
    (f : S d) (g : S e) (h : S b) :
    shufflePolynomial a (shufflePolynomial a f g) h =
      dimensionCast (add_assoc d e b).symm (shufflePolynomial a f (shufflePolynomial a g h)) := by
  rw [← shuffle_assoc_cast,dimensionCast_trans]
  rfl

@[simp] lemma shufflePolynomial_zero_left (a : I → I → ℕ) (d e : I → ℕ) (g : S e) :
    shufflePolynomial a (0 : S d) g = 0 := by
  exact LinearMap.congr_fun (map_zero (shuffleLinear a d e)) g
@[simp] lemma shufflePolynomial_zero_right (a : I → I → ℕ) (d e : I → ℕ) (f : S d) :
    shufflePolynomial a f (0 : S e) = 0 := (shuffleLinear a d e f).map_zero

lemma destabilizing_shuffle_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) {f : S d}
    (hf : f ∈ destabilizingSpace a (slope c η) d) (g : S e) :
    shufflePolynomial a f g ∈ destabilizingSpace a (slope c η) (d+e) := by
  induction hf using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨u,v,h,f₁,g',hu,hv,hμ,rfl⟩ := hF
    subst d
    refine Submodule.subset_span ⟨u,v+e,(add_assoc u v e).symm,f₁,
      shufflePolynomial a g' g,hu,add_ne_zero_left v e hv,?_,?_⟩
    · rw [slope_add_same c η hc hs]
      exact hμ
    · exact shuffle_assoc_cast_symm a f₁ g' g
  | zero => simp
  | add f f' hf hf' ih ih' =>
    simpa only [shufflePolynomial_add_left] using
      (destabilizingSpace a (slope c η) (d+e)).add_mem ih ih'
  | smul r f hf ih =>
    simpa only [shufflePolynomial_smul_left] using
      (destabilizingSpace a (slope c η) (d+e)).smul_mem r ih

lemma destabilizing_shuffle_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (f : S d)
    {g : S e} (hg : g ∈ destabilizingSpace a (slope c η) e) :
    shufflePolynomial a f g ∈ destabilizingSpace a (slope c η) (d+e) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨u,v,h,g',h',hu,hv,hμ,rfl⟩ := hg
    subst e
    refine Submodule.subset_span ⟨d+u,v,add_assoc d u v,
      shufflePolynomial a f g',h',add_ne_zero_right d u hu,hv,?_,?_⟩
    · rw [slope_add_same c η hc hs]
      apply slope_add_gt c η hc hu (mass_eq c η hc d)
      rwa [hs]
    · exact (shuffle_assoc_cast a f g' h').symm
  | zero => simp
  | add g g' hg hg' ih ih' =>
    simpa only [shufflePolynomial_add_right] using
      (destabilizingSpace a (slope c η) (d+e)).add_mem ih ih'
  | smul r g hg ih =>
    simpa only [shufflePolynomial_smul_right] using
      (destabilizingSpace a (slope c η) (d+e)).smul_mem r ih

noncomputable def shuffleB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : slope c η d = slope c η e) :
    B a (slope c η) d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) := by
  let J := destabilizingSpace a (slope c η) (d+e)
  let L : S d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) :=
    { toFun := fun f => (destabilizingSpace a (slope c η) e).mapQ J
        (shuffleLinear a d e f) (by
          intro g hg
          exact destabilizing_shuffle_right a c η hc hs f hg)
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_add_left a f g x)
      map_smul' := by
        intro r f
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_smul_left a r f x) }
  exact (destabilizingSpace a (slope c η) d).liftQ L (by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro g
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (destabilizing_shuffle_left a c η hc hs hf g))

@[simp] lemma shuffleB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : slope c η d = slope c η e) (f : S d) (g : S e) :
    shuffleB a c η hc d e hs ((destabilizingSpace a (slope c η) d).mkQ f)
      ((destabilizingSpace a (slope c η) e).mkQ g) =
    (destabilizingSpace a (slope c η) (d+e)).mkQ (shufflePolynomial a f g) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ExtendPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

@[reducible] def Centers : SplitTree I → Type
  | .leaf _ => Unit
  | .node l r => l.Centers ⊕ r.Centers

noncomputable def centerTranslation (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    (τ : ∀ d, A d →ₐ[ℚ] Polynomial (A d)) :
    (T : SplitTree I) → tensor A T →ₐ[ℚ] MvPolynomial T.Centers (tensor A T)
  | .leaf d => ((Polynomial.toMvPolynomial ()).restrictScalars ℚ).comp (τ d)
  | .node l r =>
    let L := (extendPolynomial (Algebra.TensorProduct.includeLeft :
      tensor A l →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inl).comp (centerTranslation A τ l)
    let R := (extendPolynomial (Algebra.TensorProduct.includeRight :
      tensor A r →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inr).comp (centerTranslation A τ r)
    Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => mul_comm (L x) (R y))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma centerTranslation_tmul (A : (I → ℕ) → CommAlgCat.{u} ℚ)
    (τ : ∀ d, A d →ₐ[ℚ] Polynomial (A d)) (l r : SplitTree I)
    (x : tensor A l) (y : tensor A r) :
    centerTranslation A τ (.node l r) (x ⊗ₜ[ℚ] y) =
      extendPolynomial (Algebra.TensorProduct.includeLeft :
        tensor A l →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inl (centerTranslation A τ l x) *
      extendPolynomial (Algebra.TensorProduct.includeRight :
        tensor A r →ₐ[ℚ] tensor A l ⊗[ℚ] tensor A r) Sum.inr (centerTranslation A τ r y) := by
  rfl

noncomputable def centeredRestrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) :
    B a (SlopeArithmetic.slope c η) T.dim →ₐ[ℚ]
      MvPolynomial T.Centers (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T) :=
  (centerTranslation (quotientFamily a (SlopeArithmetic.slope c η))
    (taylorB a (SlopeArithmetic.slope c η)) T).comp (restrictionB a c η hc θ T h)

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TaylorSCoeffHomogeneous
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

@[simp] lemma taylorB_coeff_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) : (taylorB a μ d f).coeff 0=f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (taylorB a μ d (quotientAlg a μ d f)).coeff 0=quotientAlg a μ d f
    rw [taylorB_mk,Polynomial.coeff_map]
    apply congrArg (quotientAlg a μ d)
    apply Subtype.ext
    have h := congrArg (fun p : Polynomial (MvPolynomial (Σ i,Fin (d i)) ℚ)=>p.coeff 0)
      (map_taylorSValue d f)
    rw [Polynomial.coeff_map,taylor_coeff_zero] at h
    change ((taylorSValue d f).coeff 0).val=f.val
    exact h

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

@[reducible] def Degrees : SplitTree I → Type
  | .leaf _ => ℤ
  | .node l r => l.Degrees × r.Degrees

@[reducible] def totalDegree : (T : SplitTree I) → T.Degrees → ℤ
  | .leaf _, k => k
  | .node l r, k => l.totalDegree k.1 + r.totalDegree k.2

@[reducible] def NonnegativeDegree : (T : SplitTree I) → T.Degrees → Prop
  | .leaf _, k => 0≤k
  | .node l r, k => l.NonnegativeDegree k.1 ∧ r.NonnegativeDegree k.2

noncomputable def componentTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    (T : SplitTree I) → T.Degrees →
      tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T
  | .leaf d, k => componentB a μ d k
  | .node l r, k => TensorProduct.map (componentTensor a μ l k.1) (componentTensor a μ r k.2)

@[reducible] def IsOrderedList : SplitTree I → Prop
  | .leaf _ => True
  | .node (.leaf _) r => r.IsOrderedList
  | .node (.node _ _) _ => False

@[reducible] def doubleShift (a : I → I → ℕ) : SplitTree I → ℤ
  | .leaf d => eulerForm a d d
  | .node l r => l.doubleShift a + r.doubleShift a

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialCoeffLinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

noncomputable def relativeCoeffB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) (s : ℕ) :
    B a μ d ⊗[ℚ] B a μ e →ₗ[ℚ] B a μ d ⊗[ℚ] B a μ e :=
  (polynomialCoeffLinear (B a μ d ⊗[ℚ] B a μ e) s).comp
    (relativeTaylorB a μ d e).toLinearMap

@[simp] lemma relativeCoeffB_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (s : ℕ) (f : B a μ d) (g : B a μ e) :
    relativeCoeffB a μ d e s (f ⊗ₜ[ℚ] g)=(taylorB a μ d f).coeff s ⊗ₜ[ℚ] g := by
  change (relativeTaylorB a μ d e (f ⊗ₜ[ℚ] g)).coeff s=_
  rw [relativeTaylorB_tmul,Polynomial.coeff_mul_C,Polynomial.coeff_map]
  change ((taylorB a μ d f).coeff s ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] g)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Degree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

omit [Fintype I] [DecidableEq I] in
lemma componentS_zero (d : I → ℕ) (f : S d) :
    componentS d 0 f=algebraMap ℚ (S d) (constantCoeff f.val) := by
  apply Subtype.ext
  exact constantWeight_component_zero f.val

omit [Fintype I] [DecidableEq I] in
lemma componentS_zero_mul (d : I → ℕ) (f g : S d) :
    componentS d 0 (f*g)=componentS d 0 f*componentS d 0 g := by
  rw [componentS_zero,componentS_zero,componentS_zero]
  change algebraMap ℚ (S d) (constantCoeff (f.val*g.val))=_
  rw [map_mul,map_mul]

noncomputable def degreeZeroB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    B a μ d →ₐ[ℚ] B a μ d where
  toFun := componentB a μ d 0
  map_zero' := (componentB a μ d 0).map_zero
  map_add' := (componentB a μ d 0).map_add
  map_one' := by
    change componentB a μ d 0 (quotientAlg a μ d 1)=quotientAlg a μ d 1
    change quotientAlg a μ d (componentS d 0 1)=_
    rw [componentS_zero]
    change quotientAlg a μ d (algebraMap ℚ (S d) (constantCoeff 1))=_
    simp only [map_one]
  map_mul' x y := by
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      induction y using Submodule.Quotient.induction_on with
      | H g =>
        change componentB a μ d 0 (quotientAlg a μ d f*quotientAlg a μ d g)=_
        rw [←map_mul]
        change quotientAlg a μ d (componentS d 0 (f*g))=
          quotientAlg a μ d (componentS d 0 f)*quotientAlg a μ d (componentS d 0 g)
        rw [componentS_zero_mul,map_mul]
  commutes' q := by
    change componentB a μ d 0 (quotientAlg a μ d (algebraMap ℚ (S d) q))=
      quotientAlg a μ d (algebraMap ℚ (S d) q)
    change quotientAlg a μ d (componentS d 0 (algebraMap ℚ (S d) q))=_
    rw [componentS_zero]
    change quotientAlg a μ d (algebraMap ℚ (S d) (constantCoeff (C q)))=_
    rw [constantCoeff_C]

@[simp] lemma degreeZeroB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (f : S d) :
    degreeZeroB a μ d (quotientAlg a μ d f)=algebraMap ℚ (B a μ d) (constantCoeff f.val) := by
  change quotientAlg a μ d (componentS d 0 f)=_
  rw [componentS_zero,AlgHom.commutes]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ShuffleUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.taylorB_coeff_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [DecidableEq I] [∀ i,Fintype (A i)] in
lemma labeledValue_unit (s : Pack (A:=A)) :
    labeledValue (1 : S (0 : I → ℕ)) s=if s=(fun _=>∅) then 1 else 0 := by
  classical
  by_cases hs : s=(fun _=>∅)
  · subst s
    simp [labeledValue,valueAt]
  · have h : ¬∀ i,(s i).card=(0 : I → ℕ) i := by
      intro h
      exact hs (funext fun i=>Finset.card_eq_zero.mp (h i))
    simp only [labeledValue,dite_eq_right h,ite_eq_right hs]

lemma shuffle_labeled_unit_left (a : I → I → ℕ) (d : I → ℕ) (f : S d)
    (s : Pack (A:=A)) :
    PackConvolution.shuffle (pairKernel a) (labeledValue (1 : S (0 : I → ℕ)))
      (labeledValue f) s=labeledValue f s := by
  classical
  unfold PackConvolution.shuffle
  rw [Finset.sum_eq_single (emptyLeftCut s)]
  · have hL : left (emptyLeftCut s)=fun _=>∅ := rfl
    have hR : right (emptyLeftCut s)=s := rfl
    rw [labeledValue_unit,ite_eq_left hL,hR]
    simp [hL,PackConvolution.kernel]
  · intro p hp hne
    have h : left p≠(fun _=>∅) := fun hh=>hne (eq_emptyLeftCut p hh)
    simp only [labeledValue_unit,ite_eq_right h,zero_mul]
  · simp

lemma shuffle_labeled_unit_right (a : I → I → ℕ) (d : I → ℕ) (f : S d)
    (s : Pack (A:=A)) :
    PackConvolution.shuffle (pairKernel a) (labeledValue f)
      (labeledValue (1 : S (0 : I → ℕ))) s=labeledValue f s := by
  classical
  unfold PackConvolution.shuffle
  rw [Finset.sum_eq_single (emptyRightCut s)]
  · have hR : right (emptyRightCut s)=fun _=>∅ := rfl
    have hL : left (emptyRightCut s)=s := rfl
    rw [labeledValue_unit,ite_eq_left hR,hL]
    simp [hR,PackConvolution.kernel]
  · intro p hp hne
    have h : right p≠(fun _=>∅) := fun hh=>hne (eq_emptyRightCut p hh)
    simp only [labeledValue_unit,ite_eq_right h,mul_zero,zero_mul]
  · simp

lemma shufflePolynomial_unit_left (a : I → I → ℕ) (d : I → ℕ) (f : S d) :
    shufflePolynomial a (1 : S (0 : I → ℕ)) f=castS (zero_add d).symm f := by
  classical
  let s : Pack (A:=fun i=>Fin ((0+d) i)) := fun _=>Finset.univ
  let r : Realization (0+d) s := defaultRealization (by intro i; simp [s])
  apply labeledValue_injective r
  dsimp only
  rw [labeledValue_shuffle,labeledValue_cast]
  exact shuffle_labeled_unit_left a d f s

lemma shufflePolynomial_unit_right (a : I → I → ℕ) (d : I → ℕ) (f : S d) :
    shufflePolynomial a f (1 : S (0 : I → ℕ))=castS (add_zero d).symm f := by
  classical
  let s : Pack (A:=fun i=>Fin ((d+0) i)) := fun _=>Finset.univ
  let r : Realization (d+0) s := defaultRealization (by intro i; simp [s])
  apply labeledValue_injective r
  dsimp only
  rw [labeledValue_shuffle,labeledValue_cast]
  exact shuffle_labeled_unit_right a d f s

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma S_zero_eq_scalar (f : S (0 : I → ℕ)) :
    f=constantCoeff f.val • (1 : S (0 : I → ℕ)) := by
  let : IsEmpty (Σi : I, Fin ((0 : I → ℕ) i)) := ⟨fun x => Fin.elim0 x.2⟩
  rw [←Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact eq_C_of_isEmpty f.val

lemma destabilizingSpace_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    destabilizingSpace a μ 0=⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro f ⟨u,v,h,f',g',hu,hv,_,_⟩
  exact (hu (add_eq_zero.mp h).1).elim

lemma castS_mem_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) {f : S d} (hf : f∈destabilizingSpace a μ d) :
    castS h f∈destabilizingSpace a μ e := by
  subst e
  exact hf

lemma destabilizing_shuffle_unit_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    {f : S d} (hf : f∈destabilizingSpace a (slope c η) d) (g : S e) :
    shufflePolynomial a f g∈destabilizingSpace a (slope c η) (d+e) := by
  rcases hs with rfl|rfl|hs
  · rw [destabilizingSpace_zero] at hf
    have hf0 : f=0 := hf
    rw [hf0,shufflePolynomial_zero_left]
    exact Submodule.zero_mem _
  · rw [S_zero_eq_scalar g,shufflePolynomial_smul_right,shufflePolynomial_unit_right]
    exact Submodule.smul_mem _ _ (castS_mem_destabilizing a _ _ hf)
  · exact destabilizing_shuffle_left a c η hc hs hf g

lemma destabilizing_shuffle_unit_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (f : S d) {g : S e} (hg : g∈destabilizingSpace a (slope c η) e) :
    shufflePolynomial a f g∈destabilizingSpace a (slope c η) (d+e) := by
  rcases hs with rfl|rfl|hs
  · rw [S_zero_eq_scalar f,shufflePolynomial_smul_left,shufflePolynomial_unit_left]
    exact Submodule.smul_mem _ _ (castS_mem_destabilizing a _ _ hg)
  · rw [destabilizingSpace_zero] at hg
    have hg0 : g=0 := hg
    rw [hg0,shufflePolynomial_zero_right]
    exact Submodule.zero_mem _
  · exact destabilizing_shuffle_right a c η hc hs f hg

noncomputable def shuffleBUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) := by
  let J := destabilizingSpace a (slope c η) (d+e)
  let L : S d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) :=
    { toFun := fun f => (destabilizingSpace a (slope c η) e).mapQ J
        (shuffleLinear a d e f) (by
          intro g hg
          exact destabilizing_shuffle_unit_right a c η hc hs f hg)
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_add_left a f g x)
      map_smul' := by
        intro r f
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_smul_left a r f x) }
  exact (destabilizingSpace a (slope c η) d).liftQ L (by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro g
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (destabilizing_shuffle_unit_left a c η hc hs hf g))

@[simp] lemma shuffleBUnit_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S d) (g : S e) :
    shuffleBUnit a c η hc d e hs ((destabilizingSpace a (slope c η) d).mkQ f)
      ((destabilizingSpace a (slope c η) e).mkQ g) =
    (destabilizingSpace a (slope c η) (d+e)).mkQ (shufflePolynomial a f g) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance tensorSCommRing (d e : I → ℕ) : CommRing (S d ⊗[ℚ] S e) := inferInstance
noncomputable local instance tensorSAlgebra (d e : I → ℕ) : Algebra ℚ (S d ⊗[ℚ] S e) := inferInstance
noncomputable local instance fourSCommRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) := inferInstance
noncomputable local instance fourSAlgebra (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) := inferInstance

noncomputable def fourValueAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) →ₐ[ℚ]
      MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toAlgHom.comp
    (Algebra.TensorProduct.map (tensorValueAlg d₁ e₁) (tensorValueAlg d₂ e₂))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma fourValueAlg_apply (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    fourValueAlg d₁ e₁ d₂ e₂ x=fourValue d₁ e₁ d₂ e₂ x := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
namespace SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def renameSeries (d e : I → ℕ) (σ : CellGroup d e) :
    LaurentSeries (MvPolynomial (CellVars d e) ℚ) →+*
      LaurentSeries (MvPolynomial (CellVars d e) ℚ) :=
  mapRing (rename (cellAction d e σ)).toRingHom

omit [Fintype I] in
lemma rename_rawFactor (a : I → I → ℕ) (d e : I → ℕ)
    (σ : CellGroup d e) (i j : I) (x : Fin (d i)) (y : Fin (e j)) :
    Units.map (renameSeries d e σ).toMonoidHom (rawFactor a d e i j x y)=
      rawFactor a d e i j (σ.1 i x) (σ.2 j y) := by
  unfold rawFactor renameSeries
  rw [map_zpow,affineUnit_map]
  congr 2
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,map_sub,rename_X]
  rfl

lemma rawInverseKernelUnit_symmetric (a : I → I → ℕ) (d e : I → ℕ)
    (σ : CellGroup d e) :
    Units.map (renameSeries d e σ).toMonoidHom
      (rawInverseKernelUnit a d e)=rawInverseKernelUnit a d e := by
  simp only [rawInverseKernelUnit,map_prod,rename_rawFactor]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  calc
    _ = ∏ x : Fin (d i), ∏ y : Fin (e j), rawFactor a d e i j (σ.1 i x) y := by
      exact Finset.prod_congr rfl (fun x hx=>Equiv.prod_comp (σ.2 j) _)
    _ = _ := Equiv.prod_comp (σ.1 i) (fun x : Fin (d i)=>∏ y : Fin (e j), rawFactor a d e i j x y)

def IsSeparate (d e : I → ℕ) (f : LaurentSeries (MvPolynomial (CellVars d e) ℚ)) : Prop :=
  ∀ σ : CellGroup d e, renameSeries d e σ f=f

lemma realize_separateSeries (d e : I → ℕ)
    (f : LaurentSeries (MvPolynomial (CellVars d e) ℚ)) (hf : IsSeparate d e f) :
    mapRing (R:=S d ⊗[ℚ] S e) (S:=MvPolynomial (CellVars d e) ℚ) (tensorValueAlg d e).toRingHom (separateSeries d e f)=f := by
  apply HahnSeries.ext
  funext k
  apply tensorValue_separateTensor
  intro σ
  exact congrArg (fun p : LaurentSeries (MvPolynomial (CellVars d e) ℚ)=>p.coeff k) (hf σ)

noncomputable def liftSeparateUnit (d e : I → ℕ)
    (f : (LaurentSeries (MvPolynomial (CellVars d e) ℚ))ˣ)
    (hf : ∀ σ : CellGroup d e, Units.map
      (renameSeries d e σ).toMonoidHom f=f) :
    (LaurentSeries (S d ⊗[ℚ] S e))ˣ where
  val := separateSeries d e f
  inv := separateSeries d e (↑f⁻¹)
  val_inv := by
    apply realize_injective d e
    rw [map_mul,map_one,realize_separateSeries,realize_separateSeries]
    · exact f.val_inv
    · intro σ
      exact congrArg Units.val (by simpa only [map_inv] using congrArg Inv.inv (hf σ))
    · intro σ
      exact congrArg Units.val (hf σ)
  inv_val := by
    apply realize_injective d e
    rw [map_mul,map_one,realize_separateSeries,realize_separateSeries]
    · exact f.inv_val
    · intro σ
      exact congrArg Units.val (hf σ)
    · intro σ
      exact congrArg Units.val (by simpa only [map_inv] using congrArg Inv.inv (hf σ))

noncomputable def inverseKernelUnit (a : I → I → ℕ) (d e : I → ℕ) :
    (LaurentSeries (S d ⊗[ℚ] S e))ˣ :=
  liftSeparateUnit d e (rawInverseKernelUnit a d e) (rawInverseKernelUnit_symmetric a d e)

noncomputable def quotientInverseKernelUnit (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    (LaurentSeries (B a μ d ⊗[ℚ] B a μ e))ˣ :=
  Units.map (mapRing (R:=S d ⊗[ℚ] S e) (S:=B a μ d ⊗[ℚ] B a μ e) (Algebra.TensorProduct.map (quotientAlg a μ d)
    (quotientAlg a μ e)).toRingHom).toMonoidHom (inverseKernelUnit a d e)

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourTensorKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance cancelTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance cancelTensorDistrib (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
noncomputable local instance cancelTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance cancelFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance cancelFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

noncomputable local instance cancelTensorSelf (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance cancelTensorNonUnital (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (cancelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance cancelFourNonUnital (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (cancelFourRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring

noncomputable local instance cancelSeriesRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SeparationCoefficients
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SeparationInfinity

noncomputable def separationCoefficient (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (j : ℤ) :
    B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e :=
  (mulPolynomialCoeff (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) d e).val j).comp
    (restrictionRelativeB a c η hc hs (firstCut d e)).toLinearMap

@[simp] lemma separationCoefficient_apply (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (j : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    separationCoefficient a c η hc hs j f =
      mulPolynomialCoeff (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) d e).val j
        (restrictionRelativeB a c η hc hs (firstCut d e) f) := rfl

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Restriction
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma castS_trans {d e b : I → ℕ} (h : d=e) (k : e=b) (f : S d) :
    castS k (castS h f)=castS (h.trans k) f := by subst e; subst b; rfl
omit [Fintype I] [DecidableEq I] in
@[simp] lemma castS_rfl {d : I → ℕ} (f : S d) : castS rfl f=f := rfl

def castB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d e : I → ℕ} (h : d=e)
    (f : B a μ d) : B a μ e := h ▸ f

@[simp] lemma castB_rfl (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d : I → ℕ}
    (f : B a μ d) : castB a μ rfl f=f := rfl

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
open MvPolynomial
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

def SlopeEulerSymmetric (a : I → I → ℕ) (c η : I → ℝ) (θ : ℝ) : Prop :=
  ∀ d e : I → ℕ, d≠0 → e≠0 → SlopeArithmetic.slope c η d=θ →
    SlopeArithmetic.slope c η e=θ → eulerForm a d e=eulerForm a e d

end ElementaryPositivity.RawShuffle

end

end OAI
end


