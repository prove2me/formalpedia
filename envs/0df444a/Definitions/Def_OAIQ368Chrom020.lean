-- Prove2me | Definitions.Def_OAIQ368Chrom020
-- name    : OAIQ368Chrom020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:11:37.28317+00:00
-- url     : https://prove2.me/theorems/d5d91fa3-5808-482a-bd85-fa23be3b603b
-- title:
--   Definitions bundle OAIQ368Chrom020 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 3 definitions and 22 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.rawFactor`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.rawInverseKernelUnit`, `OAI.ElementaryPositivity.RawShuffle.crossClearing`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_CanonicalCard`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CanonicalCard.lean), [`Chromatic_Shuffle_CellVars`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellVars.lean), [`Chromatic_Shuffle_CrossDifference`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CrossDifference.lean), [`Chromatic_Shuffle_LaurentKernel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/LaurentKernel.lean), [`Chromatic_Shuffle_RestrictionB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/RestrictionB.lean), [`Chromatic_Shuffle_TargetEmbedding`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TargetEmbedding.lean), [`Chromatic_Walls_Mass`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/Mass.lean), [`Chromatic_Walls_ShuffleTensorLinear`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/ShuffleTensorLinear.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom017` and `OAIQ368Chrom018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom022`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom017
import Definitions.Def_OAIQ368Chrom018

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossDifference
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
lemma map_taylorS_left (d e : I → ℕ) (f : S d) :
    Polynomial.map (tensorValueAlg d e).toRingHom
      (Polynomial.map (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e).toRingHom
        (taylorS d f)) =
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor f.val) := by
  rw [← map_taylorS d f,Polynomial.map_map,Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro g
  change tensorValue d e (g ⊗ₜ[ℚ] 1) = rename Sum.inl g.val
  simp

noncomputable def crossClearing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
  Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e (crossTensor d e))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ShuffleTensorLinear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma shuffleTensorLinear_mem (a : I → I → ℕ) (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    shuffleTensorLinear a d e f ∈ shuffleImage a d e := by
  induction f using OAI.tensorInductionOn with
  | tmul f g => exact Submodule.subset_span ⟨f,g,rfl⟩
  | add f g hf hg => simpa only [map_add] using (shuffleImage a d e).add_mem hf hg

lemma shuffleImage_le_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (hd : d≠0) (he : e≠0) (hμ : μ d > μ (d+e)) :
    shuffleImage a d e ≤ destabilizingSpace a μ (d+e) := by
  apply Submodule.span_le.mpr
  rintro p ⟨f,g,rfl⟩
  exact Submodule.subset_span ⟨d,e,rfl,f,g,hd,he,hμ,rfl⟩

lemma quotient_shuffleTensorLinear_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (hd : d≠0) (he : e≠0) (hμ : μ d > μ (d+e))
    (f : S d ⊗[ℚ] S e) : quotientAlg a μ (d+e) (shuffleTensorLinear a d e f) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((shuffleImage_le_destabilizing a μ d e hd he hμ) (shuffleTensorLinear_mem a d e f))

lemma quotient_twoTargetTransfer_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h : (d₁≠0 ∧ e₁≠0 ∧ μ d₁ > μ (d₁+e₁)) ∨
         (d₂≠0 ∧ e₂≠0 ∧ μ d₂ > μ (d₂+e₂)))
    (f : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    quotientTensor a μ (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ f) = 0 := by
  induction f using OAI.tensorInductionOn with
  | tmul f g =>
    simp only [twoTargetTransfer, TensorProduct.map_tmul, quotientTensor,
      Algebra.TensorProduct.map_tmul]
    rcases h with ⟨hd,he,hμ⟩ | ⟨hd,he,hμ⟩
    · rw [quotient_shuffleTensorLinear_zero a μ d₁ e₁ hd he hμ,TensorProduct.zero_tmul]
    · rw [quotient_shuffleTensorLinear_zero a μ d₂ e₂ hd he hμ,TensorProduct.tmul_zero]
  | add f g hf hg =>
    change (quotientTensor a μ (d₁+e₁) (d₂+e₂)).toLinearMap (twoTargetTransfer a d₁ e₁ d₂ e₂ (f+g)) = 0
    rw [(twoTargetTransfer a d₁ e₁ d₂ e₂).map_add, (quotientTensor a μ (d₁+e₁) (d₂+e₂)).toLinearMap.map_add]
    exact (congrArg₂ (· + ·) hf hg).trans (add_zero 0)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellVars
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

variable [Fintype I] [DecidableEq I]

lemma quotient_cellTransfer_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h : (d₁≠0 ∧ e₁≠0 ∧ μ d₁ > μ (d₁+e₁)) ∨
         (d₂≠0 ∧ e₂≠0 ∧ μ d₂ > μ (d₂+e₂)))
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a μ (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p) = 0 :=
  quotient_twoTargetTransfer_zero a μ d₁ e₁ d₂ e₂ h _

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma localizeTensor_injective (d e : I → ℕ) : Function.Injective (localizeTensor d e) := by
  intro f g h
  apply tensorValue_injective d e
  exact IsFractionRing.injective _ (FractionRing (MvPolynomial (CellVars d e) ℚ)) h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TargetEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

lemma quotientTensor_cast_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (t : S d ⊗[ℚ] S e)
    (ht : quotientTensor a μ d e t = 0) :
    quotientTensor a μ d' e' (castTensor h k t) = 0 := by
  subst d'
  subst e'
  exact ht

lemma targetValueAt_injective {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    Function.Injective (targetValueAt p R T) :=
  (renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective).injective.comp
    (localizeTensor_injective d e)

omit [Fintype I] [DecidableEq I] in
lemma targetValueAt_mul {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (f g : S d ⊗[ℚ] S e) :
    targetValueAt p R T (f*g) = targetValueAt p R T f * targetValueAt p R T g := by
  change renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
    (algebraMap (MvPolynomial (CellVars d e) ℚ) (FractionRing (MvPolynomial (CellVars d e) ℚ))
      (tensorValue d e (f*g))) = _
  rw [tensorValue_mul,map_mul,map_mul]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Mass
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma mass_pos (c : I → ℝ) (hc : ∀ i,0 < c i) (d : I → ℕ) (hd : d ≠ 0) :
    0 < mass c d := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,d i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hd
    funext i
    exact hn i
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (Nat.cast_nonneg _) (hc j).le
  · exact ⟨i,Finset.mem_univ _,mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (hc i)⟩

lemma mass_eq (c η : I → ℝ) (hc : ∀ i,0 < c i) (d : I → ℕ) :
    mass η d = slope c η d * mass c d := by
  by_cases hd : d=0
  · subst d; simp
  · exact (div_mul_cancel₀ _ (mass_pos c hc d hd).ne').symm

lemma slope_add (c η : I → ℝ) (hc : ∀ i,0 < c i) {d e : I → ℕ}
    (hd : d ≠ 0) (hs : slope c η d = slope c η e) :
    slope c η (d+e) = slope c η d := by
  apply (div_eq_iff (mass_pos c hc (d+e) (add_ne_zero_left d e hd)).ne').mpr
  rw [mass_add,mass_add,mass_eq c η hc d,mass_eq c η hc e,← hs]
  ring

lemma slope_add_same (c η : I → ℝ) (hc : ∀ i,0 < c i) {d e : I → ℕ}
    (hs : slope c η d = slope c η e) :
    slope c η (d+e) = slope c η d := by
  by_cases hd : d=0
  · subst d
    simpa using hs.symm
  · exact slope_add c η hc hd hs

lemma slope_add_gt (c η : I → ℝ) (hc : ∀ i,0 < c i) {d u : I → ℕ}
    (hu : u ≠ 0) {θ : ℝ} (hd : mass η d = θ * mass c d)
    (hs : slope c η u > θ) : slope c η (d+u) > θ := by
  have hmass := mass_pos c hc u hu
  have hu' : mass η u > θ * mass c u := (lt_div_iff₀ hmass).mp hs
  apply (lt_div_iff₀ (mass_pos c hc (d+u) (add_ne_zero_right d u hu))).mpr
  rw [mass_add,mass_add,hd,mul_add]
  linarith

end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma destabilized_target (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hs : slope c η (d₁+e₁) = slope c η (d₂+e₂))
    (hd : d₁+d₂≠0) (hμ : slope c η (d₁+d₂) > slope c η (d₁+e₁)) :
    (d₁≠0 ∧ e₁≠0 ∧ slope c η d₁ > slope c η (d₁+e₁)) ∨
    (d₂≠0 ∧ e₂≠0 ∧ slope c η d₂ > slope c η (d₂+e₂)) := by
  have ht : mass η (d₁+d₂) > slope c η (d₁+e₁) * mass c (d₁+d₂) :=
    (lt_div_iff₀ (mass_pos c hc _ hd)).mp hμ
  rw [mass_add,mass_add,mul_add] at ht
  have hex : mass η d₁ > slope c η (d₁+e₁) * mass c d₁ ∨
      mass η d₂ > slope c η (d₂+e₂) * mass c d₂ := by
    rw [← hs]
    by_contra hn
    push Not at hn
    linarith
  rcases hex with h | h
  · left
    have hdn : d₁≠0 := by intro hh; simp [hh] at h
    have hen : e₁≠0 := by
      intro hh
      rw [hh,add_zero,mass_eq c η hc d₁] at h
      exact (lt_irrefl _ h)
    exact ⟨hdn,hen,(lt_div_iff₀ (mass_pos c hc _ hdn)).mpr h⟩
  · right
    have hdn : d₂≠0 := by intro hh; simp [hh] at h
    have hen : e₂≠0 := by
      intro hh
      rw [hh,add_zero,mass_eq c η hc d₂] at h
      exact (lt_irrefl _ h)
    exact ⟨hdn,hen,(lt_div_iff₀ (mass_pos c hc _ hdn)).mpr h⟩
end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CanonicalCard
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

omit [Fintype I] [DecidableEq I] in
lemma canonical_source_card (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :
    ((left (canonicalLeftCut d₁ e₁ d₂ e₂) i) ∪
      (left (canonicalRightCut d₁ e₁ d₂ e₂) i)).card = d₁ i + d₂ i := by
  have hd : Disjoint (left (canonicalLeftCut d₁ e₁ d₂ e₂) i)
      (left (canonicalRightCut d₁ e₁ d₂ e₂) i) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases x with (x|x) <;>
      simp [canonicalLeftCut,canonicalRightCut,sumPackCut,embedPackCut,left] at hx hy
  rw [Finset.card_union_of_disjoint hd]
  simp [canonicalLeftCut,canonicalRightCut,sumPackCut,embedPackCut,left]

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma targetValueAt_smul {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (r : ℚ) (t : S d ⊗[ℚ] S e) :
    targetValueAt p R T (r • t) = r • targetValueAt p R T t :=
  map_rat_smul (targetValueAt p R T) r t

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma quotientTensor_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : S d) (g : S e) :
    quotientTensor a μ d e (f ⊗ₜ[ℚ] g) = quotientAlg a μ d f ⊗ₜ[ℚ] quotientAlg a μ e g := rfl

lemma relativeTaylor_quotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (t : S d ⊗[ℚ] S e) :
    Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e t) =
      relativeTaylorB a μ d e (quotientTensor a μ d e t) := by
  induction t using OAI.tensorInductionOn with
  | tmul f g =>
    rw [relativeTaylor_tmul,quotientTensor_tmul,relativeTaylorB_tmul,taylorB_mk,
      Polynomial.map_mul,Polynomial.map_C]
    have hr : (quotientTensor a μ d e).toRingHom (1 ⊗ₜ[ℚ] g) = 1 ⊗ₜ[ℚ] quotientAlg a μ e g := by
      change quotientAlg a μ d 1 ⊗ₜ[ℚ] quotientAlg a μ e g = _
      rw [map_one]
    rw [hr]
    congr 1
    rw [Polynomial.map_map,Polynomial.map_map]
    congr 1
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]

lemma quotient_relativeTaylor_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (t : S d ⊗[ℚ] S e) (h : quotientTensor a μ d e t = 0) :
    Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e t) = 0 := by
  rw [relativeTaylor_quotient,h,map_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

noncomputable def rawFactor (a : I → I → ℕ) (d e : I → ℕ)
    (i j : I) (x : Fin (d i)) (y : Fin (e j)) :
    (LaurentSeries (MvPolynomial (CellVars d e) ℚ))ˣ :=
  affineUnit (X (Sum.inr ⟨j,y⟩)-X (Sum.inl ⟨i,x⟩)) ^ inverseExponent a i j

noncomputable def rawInverseKernelUnit (a : I → I → ℕ) (d e : I → ℕ) :
    (LaurentSeries (MvPolynomial (CellVars d e) ℚ))ˣ :=
  ∏ i, ∏ j, ∏ x : Fin (d i), ∏ y : Fin (e j), rawFactor a d e i j x y

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictionB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
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

omit [Fintype I] [DecidableEq I] in
lemma dimensionCast_eq_castS {d e : I → ℕ} (h : d=e) (f : S d) :
    dimensionCast h f = castS h f := by subst e; rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end


