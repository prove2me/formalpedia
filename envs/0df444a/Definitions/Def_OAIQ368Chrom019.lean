-- Prove2me | Definitions.Def_OAIQ368Chrom019
-- name    : OAIQ368Chrom019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:11:36.059275+00:00
-- url     : https://prove2.me/theorems/be21b4c6-cad9-4b84-af78-4f6120b53e10
-- title:
--   Definitions bundle OAIQ368Chrom019 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 1 definition and 6 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.embedRealization`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_CrossDifference`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CrossDifference.lean), [`Chromatic_Shuffle_LabeledPolynomial`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/LabeledPolynomial.lean), [`Chromatic_Shuffle_QuotientAlg`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/QuotientAlg.lean).
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_QuotientAlg
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.fourValue_tmul _root_.OAI.ElementaryPositivity.RawShuffle.labeledPolynomial_algebraMap _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_fourValue _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_product _root_.OAI.ElementaryPositivity.RawShuffle.shuffleTensorLinear_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor _root_.OAI.ElementaryPositivity.RawShuffle.twoTargetTransfer_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma relativeTaylor_eval (d e : I → ℕ) (f : S d ⊗[ℚ] S e) (t : ℚ) :
    (relativeTaylor d e f).eval (algebraMap ℚ (S d ⊗[ℚ] S e) t) =
      TensorProduct.map (translationS d t) (LinearMap.id : S e →ₗ[ℚ] S e) f := by
  induction f using OAI.tensorInductionOn with
  | tmul f g =>
    rw [relativeTaylor_tmul,Polynomial.eval_mul,Polynomial.eval_C,
      eval_map_rat (R := S d) (T := S d ⊗[ℚ] S e) (Algebra.TensorProduct.includeLeft : S d →ₐ[ℚ] S d ⊗[ℚ] S e),taylorS_eval]
    simp
  | add f g hf hg => rw [map_add,Polynomial.eval_add,map_add,hf,hg]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossDifference
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
lemma relativeRaw_left (d e : I → ℕ) (f : MvPolynomial (Σi,Fin (d i)) ℚ) :
    relativeRaw d e (rename Sum.inl f) =
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [relativeRaw]
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,taylor_X,Polynomial.map_mul,hf]
    congr 1
    simp [relativeRaw]

omit [DecidableEq I] in
lemma relativeRaw_crossDifference (d e : I → ℕ) :
    relativeRaw d e (crossDifference d e) =
      ∏ i, ∏ x : Fin (d i), ∏ y : Fin (e i),
        (Polynomial.X + Polynomial.C (X (Sum.inl ⟨i,x⟩) - X (Sum.inr ⟨i,y⟩))) := by
  simp only [crossDifference,map_prod,map_sub]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro y hy
  simp [relativeRaw]
  ring

omit [DecidableEq I] in
lemma relativeRaw_crossDifference_monic (d e : I → ℕ) :
    (relativeRaw d e (crossDifference d e)).Monic := by
  rw [relativeRaw_crossDifference]
  apply Polynomial.monic_prod_of_monic
  intro i hi
  apply Polynomial.monic_prod_of_monic
  intro x hx
  apply Polynomial.monic_prod_of_monic
  intro y hy
  exact Polynomial.monic_X_add_C _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LabeledPolynomial
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
variable {A B : I → Type*} [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)]

noncomputable def embedRealization (φ : ∀ i,A i ↪ B i) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) : Realization d (embedPack φ s) :=
  fun i=>(r i).trans (PackEnumeration.mapEquiv (φ i) (s i))

omit [Fintype I] [DecidableEq I] [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)] in
lemma embedRealization_map (φ : ∀ i,A i ↪ B i) {d : I → ℕ}
    {s : Pack (A:=A)} (r : Realization d s) :
    realizationMap (embedRealization φ r) = packEmbedding φ ∘ realizationMap r := rfl

omit [Fintype I] [DecidableEq I] in
lemma embedPack_union (φ : ∀ i,A i ↪ B i) (s t : Pack (A:=A)) :
    embedPack φ (fun i=>s i ∪ t i) = fun i=>embedPack φ s i ∪ embedPack φ t i := by
  funext i
  exact Finset.map_union _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end


