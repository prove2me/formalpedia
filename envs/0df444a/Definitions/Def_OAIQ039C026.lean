-- Prove2me | Definitions.Def_OAIQ039C026
-- name    : OAIQ039C026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:16:42.757718+00:00
-- url     : https://prove2.me/theorems/f9c6d039-3330-492b-943a-077c9d3fdc10
-- title:
--   Definitions bundle OAIQ039C026 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 14 definitions, 2 instances and 23 theorems. The definitions and types are `OAI.Kadison.FreeMoments.Letter.enlarge`, `OAI.Kadison.FreeMoments.Letter.transport`, `OAI.Kadison.FreeMoments.reducedAlgebra`, `OAI.Kadison.HilbertCompletion.centeredEquiv`, `OAI.Kadison.HilbertCompletion.centeredMap`, `OAI.Kadison.HilbertCompletion.completeEquiv`, `OAI.Kadison.HilbertCompletion.powerEquiv`, `OAI.Kadison.HilbertCompletion.tensor`, `OAI.Kadison.HilbertCompletion.wordEquiv`, `OAI.Kadison.HilbertSequence.equiv`, `OAI.Kadison.PreHilbert.powerMap`, `OAI.Kadison.PreHilbert.wordMap`, `OAI.Kadison.ProjectionJoin.remainder`, `OAI.Kadison.TracialGNS.stageVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CoefficientForm`, `Commutator_CompletionCentered`, `Commutator_CornerAlgebra`, `Commutator_FreeMoments`, `Commutator_FreeMomentsTransport`, `Commutator_HilbertSequence`, `Commutator_MatrixGNS`, `Commutator_MatrixTowerGNS`, `Commutator_ProjectionJoin`, `Commutator_SubfactorExpectation`, `Commutator_TensorActions`, `Commutator_TensorCompletion`, `Commutator_TensorPowerCompletion`.
--
--   **Imports.** It imports the bundles `OAIQ039C003`, `OAIQ039C004`, `OAIQ039C008`, `OAIQ039C010` and `OAIQ039C011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C036`, `OAIQ039C037`, `OAIQ039C039`, `OAIQ039C040` and `OAIQ039C041`; the proofs of `OAI.Kadison.GeneratedMatrixBicommutant.in_range`, `OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann`, `OAI.Kadison.exists_separable_cstar_bicommutant`, `OAI.Kadison.finite_pairing_source_bound` and `OAI.Kadison.finite_pairing_test_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C011

section
-- module Solutions.OAIQ039_CM.Commutator_CoefficientForm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.PreHilbert

open UniformSpace Function

@[simp] lemma norm_word (E F : PreHilbert) (n : ℕ) (d : E) (x : Fin n → F) :
    ‖word E F n d x‖ = ‖d‖ * ∏ i, ‖x i‖ := by
  simp only [word, Completion.norm_coe, TensorProduct.norm_tmul, norm_pure]

@[simp] lemma inner_word (E F : PreHilbert) (n : ℕ) (d e : E) (x y : Fin n → F) :
    inner ℂ (word E F n d x) (word E F n e y) =
      inner ℂ d e * ∏ i, inner ℂ (x i) (y i) := by
  simp only [word, Completion.inner_coe, TensorProduct.inner_tmul, inner_pure]

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma tensorMap_surjective : Function.Surjective (tensorMap (E := E) (F := F)) := by
  let R := LinearMap.range (tensorMap (E := E) (F := F)).toLinearMap
  have hR : IsClosed (R : Set (Completion (Completion E ⊗[ℂ] Completion F))) :=
    (tensorMap (E := E) (F := F)).isometry.isClosedEmbedding.isClosed_range
  have hp : ∀ (x : Completion E) (y : Completion F),
      ((x ⊗ₜ[ℂ] y) : Completion (Completion E ⊗[ℂ] Completion F)) ∈ R := by
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => exact hR.preimage (by fun_prop)
    | ih x y => exact ⟨((x ⊗ₜ[ℂ] y) : Completion (E ⊗[ℂ] F)), tensorMap_coe_tmul x y⟩
  intro z
  change z ∈ R
  induction z using Completion.induction_on with
  | hp => exact hR
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [Completion.coe_add] using R.add_mem hx hy
    | tmul x y => exact hp x y

def tensor : Completion (E ⊗[ℂ] F) ≃ₗᵢ[ℂ] Completion (Completion E ⊗[ℂ] Completion F) :=
  LinearIsometryEquiv.ofSurjective tensorMap tensorMap_surjective

@[simp] lemma tensor_coe_tmul (x : E) (y : F) :
    tensor (E := E) (F := F) ((x ⊗ₜ[ℂ] y) : Completion (E ⊗[ℂ] F)) =
      (((x : Completion E) ⊗ₜ[ℂ] (y : Completion F)) : Completion (Completion E ⊗[ℂ] Completion F)) :=
  tensorMap_coe_tmul x y

end Kadison.HilbertCompletion
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CompletionCentered
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def completeEquiv [CompleteSpace E] : E ≃ₗᵢ[ℂ] Completion E :=
  LinearIsometryEquiv.ofSurjective (coeIsometry E) (by
    intro x
    induction x using Completion.induction_on with
    | hp => exact (coeIsometry E).isometry.isClosedEmbedding.isClosed_range
    | ih x => exact ⟨x,rfl⟩)

@[simp] lemma completeEquiv_apply [CompleteSpace E] (x : E) :
    completeEquiv x=(x : Completion E) := rfl

def centeredMap (Ω : E) : Completion (centered Ω) →ₗᵢ[ℂ]
    centered (Ω : Completion E) where
  toLinearMap := (map (centered Ω).subtypeₗᵢ).toLinearMap.codRestrict _ (by
    intro x
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change inner ℂ (Ω : Completion E) (map (centered Ω).subtypeₗᵢ x)=0
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      rw [map_coe, Completion.inner_coe]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)
  norm_map' x := (map (centered Ω).subtypeₗᵢ).norm_map x

@[simp] lemma centeredMap_coe (Ω : E) (x : centered Ω) :
    (centeredMap Ω (x : Completion (centered Ω)) : Completion E) =
      ((x : E) : Completion E) := map_coe _ _

lemma centeredMap_surjective (Ω : E) (hΩ : ‖Ω‖=1) :
    Function.Surjective (centeredMap Ω) := by
  let Q := centered (Ω : Completion E)
  let R : Submodule ℂ Q := LinearMap.range (centeredMap Ω).toLinearMap
  have hR : IsClosed (R : Set Q) := (centeredMap Ω).isometry.isClosedEmbedding.isClosed_range
  have hc : ∀ x : E, Q.orthogonalProjectionOnto (x : Completion E) ∈ R := by
    intro x
    let y : centered Ω := ⟨x-inner ℂ Ω x • Ω, by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hΩ]
      simp⟩
    refine ⟨(y : Completion (centered Ω)), ?_⟩
    apply Subtype.ext
    change (centeredMap Ω (y : Completion (centered Ω)) : Completion E) = _
    rw [centeredMap_coe]
    change ((x-inner ℂ Ω x • Ω : E) : Completion E) =
      (ℂ ∙ (Ω : Completion E))ᗮ.starProjection (x : Completion E)
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℂ (by simpa), Completion.coe_sub,
      Completion.coe_smul, Completion.inner_coe]
  have hd : DenseRange (fun x : E => Q.orthogonalProjectionOnto (x : Completion E)) := by
    apply (show Function.Surjective Q.orthogonalProjectionOnto from fun x =>
      ⟨x, Q.orthogonalProjectionOnto_mem_subspace_eq_self x⟩).denseRange.comp
      Completion.denseRange_coe Q.orthogonalProjectionOnto.continuous
  intro x
  change x ∈ R
  exact hR.closure_subset_iff.mpr (Set.range_subset_iff.mpr hc) (hd x)

def centeredEquiv (Ω : E) (hΩ : ‖Ω‖=1) : Completion (centered Ω) ≃ₗᵢ[ℂ]
    centered (Ω : Completion E) :=
  LinearIsometryEquiv.ofSurjective (centeredMap Ω) (centeredMap_surjective Ω hΩ)

end Kadison.HilbertCompletion
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder

lemma cornerFunctional_normalized (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0 < r)
    (hτ : τ p = (r : ℂ)) : cornerFunctional hp τ r hr 1=1 := by
  simp only [cornerFunctional_apply, corner_one, hτ, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]

lemma cornerFunctional_faithful (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0 < r)
    (hτ : ∀ a : A, τ (star a*a)=0 → a=0) (a : Corner hp)
    (ha : cornerFunctional hp τ r hr (star a*a)=0) : a=0 := by
  apply Subtype.ext
  apply hτ
  simpa only [cornerFunctional_apply, corner_mul, corner_star,
    smul_eq_zero, inv_eq_zero, hr.ne', false_or] using ha

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeMoments
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.FreeMoments

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable {S τ}

variable (hstar : ∀ a : A, τ (star a) = star (τ a))

variable (h1 : τ 1 = 1)

include h1 in
lemma generator_mem_wordSpan (i : ι) (a : A) (ha : a ∈ S i) : a ∈ wordSpan S τ := by
  have hc := word_mem_span (reduced_singleton (centerLetter h1 i a ha))
  have hs := (wordSpan S τ).smul_mem (τ a) one_mem_wordSpan
  have hd : word [centerLetter h1 i a ha] + τ a • (1 : A) = a := by
    simp [centerLetter]
  rw [← hd]
  exact (wordSpan S τ).add_mem hc hs

include h1 in
lemma generator_mul_word (i : ι) (a : A) (ha : a ∈ S i)
    (w : List (Letter S τ)) (hw : Reduced w) : a * word w ∈ wordSpan S τ := by
  cases w with
  | nil => simpa using generator_mem_wordSpan h1 i a ha
  | cons b w =>
    by_cases hc : i = b.color
    · have hab : a * b.val ∈ S i := mul_mem ha (by simpa [hc] using b.mem)
      let c := centerLetter h1 i (a * b.val) hab
      have hw' : Reduced (c :: w) := by
        apply hw.imp_head
        intro z hz
        change i ≠ z.color
        simpa [hc] using hz
      have hmem := (wordSpan S τ).add_mem (word_mem_span hw')
        ((wordSpan S τ).smul_mem (τ (a * b.val)) (word_mem_span hw.tail))
      have heq : word (c :: w) + τ (a * b.val) • word w = a * word (b :: w) := by
        simp only [word_cons, c, centerLetter, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
        exact sub_add_cancel _ _
      rwa [heq] at hmem
    · let c := centerLetter h1 i a ha
      have hw' : Reduced (c :: b :: w) := List.isChain_cons_cons.mpr ⟨hc, hw⟩
      have hmem := (wordSpan S τ).add_mem (word_mem_span hw')
        ((wordSpan S τ).smul_mem (τ a) (word_mem_span hw))
      have heq : word (c :: b :: w) + τ a • word (b :: w) = a * word (b :: w) := by
        change (a - τ a • (1 : A)) * word (b :: w) + τ a • word (b :: w) = _
        simp only [sub_mul, smul_mul_assoc, one_mul, sub_add_cancel]
      rwa [heq] at hmem

include h1 in
lemma generator_mul_span (i : ι) (a : A) (ha : a ∈ S i)
    {b : A} (hb : b ∈ wordSpan S τ) : a * b ∈ wordSpan S τ := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨w, hw, rfl⟩ := hb
    exact generator_mul_word h1 i a ha w hw
  | zero => simp only [mul_zero, Submodule.zero_mem]
  | add b c _ _ hb hc => simpa only [mul_add] using (wordSpan S τ).add_mem hb hc
  | smul z b _ hb => simpa only [mul_smul_comm] using (wordSpan S τ).smul_mem z hb

include h1 in
lemma word_mul_span (w : List (Letter S τ)) {b : A} (hb : b ∈ wordSpan S τ) :
    word w * b ∈ wordSpan S τ := by
  induction w with
  | nil => simpa using hb
  | cons a w ih =>
    simpa only [word_cons, mul_assoc] using generator_mul_span h1 a.color a.val a.mem ih

include h1 in
lemma mul_mem_wordSpan {a b : A} (ha : a ∈ wordSpan S τ) (hb : b ∈ wordSpan S τ) :
    a * b ∈ wordSpan S τ := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, _, rfl⟩ := ha
    exact word_mul_span h1 w hb
  | zero => simp only [zero_mul, Submodule.zero_mem]
  | add a c _ _ ha hc => simpa only [add_mul] using (wordSpan S τ).add_mem ha hc
  | smul z a _ ha => simpa only [smul_mul_assoc] using (wordSpan S τ).smul_mem z ha

include hstar in
lemma star_mem_wordSpan {a : A} (ha : a ∈ wordSpan S τ) : star a ∈ wordSpan S τ := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    rw [← word_reverseStar hstar]
    exact word_mem_span (Reduced.reverseStar hstar hw)
  | zero => simp only [star_zero, Submodule.zero_mem]
  | add a c _ _ ha hc => simpa only [star_add] using (wordSpan S τ).add_mem ha hc
  | smul z a _ ha => simpa only [star_smul] using (wordSpan S τ).smul_mem (star z) ha

variable (S) in

def reducedAlgebra : StarSubalgebra ℂ A where
  carrier := wordSpan S τ
  zero_mem' := (wordSpan S τ).zero_mem
  add_mem' := (wordSpan S τ).add_mem
  one_mem' := one_mem_wordSpan
  mul_mem' := mul_mem_wordSpan h1
  algebraMap_mem' z := by
    change algebraMap ℂ A z ∈ wordSpan S τ
    rw [Algebra.algebraMap_eq_smul_one]
    exact (wordSpan S τ).smul_mem z one_mem_wordSpan
  star_mem' := star_mem_wordSpan hstar

include hstar h1 in
lemma generator_le_reducedAlgebra (i : ι) : S i ≤ reducedAlgebra S hstar h1 :=
  fun a ha => generator_mem_wordSpan h1 i a ha

lemma reducedAlgebra_eq_iSup : reducedAlgebra S hstar h1 = ⨆ i, S i := by
  apply le_antisymm
  · intro a ha
    change a ∈ wordSpan S τ at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨w, hw, rfl⟩ := ha
      clear hw
      induction w with
      | nil => exact one_mem _
      | cons b w ih =>
        exact mul_mem ((le_iSup S b.color) b.mem) ih
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul z a _ ha => exact SMulMemClass.smul_mem z ha
  · exact iSup_le (fun i => generator_le_reducedAlgebra (S := S) (hstar := hstar) (h1 := h1) i)

end Kadison.FreeMoments
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeMomentsTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (U : ι → StarSubalgebra ℂ B)
  (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
  (j : A →⋆ₐ[ℂ] B) (htrace : ∀ a,ρ (j a)=τ a)
  (hSU : ∀ i a,a∈S i → j a∈U i)

def Letter.transport (a : Letter S τ) : Letter U ρ where
  color := a.color
  val := j a.val
  mem := hSU _ _ a.mem
  centered := (htrace _).trans a.centered

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def equiv : Pre ω H ≃ (ℕ →ᵇ H) where
  toFun := Pre.seq
  invFun := Pre.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance instAddCommGroupPre : AddCommGroup (Pre ω H) := (equiv ω H).addCommGroup

instance instModuleComplexPre : Module ℂ (Pre ω H) := (equiv ω H).addEquiv.module ℂ

omit [InnerProductSpace ℂ H] in
@[simp] lemma seq_add (x y : Pre ω H) (i : ℕ) : (x+y).seq i=x.seq i+y.seq i := rfl

@[simp] lemma seq_smul (r : ℂ) (x : Pre ω H) (i : ℕ) : (r • x).seq i=r • x.seq i := rfl

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

noncomputable def stageVector : Matrix I I ℂ →ₗ[ℂ] τ.GNS :=
  (algebraVector τ).comp φ.toLinearMap

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.NormalGNS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma mem_bicommutant (S : StarSubalgebra ℂ (K →L[ℂ] K)) (a : K →L[ℂ] K) :
    a∈bicommutant S ↔ a∈Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
  change a∈(StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))) ↔ _
  rw [←SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def remainder (p q : H →L[ℂ] H) : H →L[ℂ] H := Polar.leftSupport ((1-p)*q)

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SubfactorExpectation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S T : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

variable (hsub : ∀ i, T i≤S i)

def Letter.enlarge (a : Letter T τ) : Letter S τ :=
  ⟨a.color,a.val,hsub a.color a.mem,a.centered⟩

@[simp] lemma word_enlarge (w : List (Letter T τ)) :
    word (w.map (Letter.enlarge hsub))=word w := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.map_cons,word_cons,Letter.enlarge] using congrArg (a.val*·) ih

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorActions
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

open UniformSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace PreHilbert

variable (E F : PreHilbert)

def powerMap (U : E →ₗᵢ[ℂ] E) : ∀ n, power E n →ₗᵢ[ℂ] power E n
  | 0 => LinearIsometry.id
  | n+1 => TensorProduct.mapIsometry U (powerMap U n)

@[simp] lemma powerMap_pure (U : E →ₗᵢ[ℂ] E) (n : ℕ) (x : Fin n → E) :
    powerMap E U n (pure E n x) = pure E n (fun i => U (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerMap, pure_succ, TensorProduct.mapIsometry_apply,
      TensorProduct.map_tmul, LinearIsometry.coe_toLinearMap, ih]
    rfl

def wordMap (U : E →ₗᵢ[ℂ] E) (V : F →ₗᵢ[ℂ] F) (n : ℕ) :
    wordSpace E F n →ₗᵢ[ℂ] wordSpace E F n :=
  completionIsometry (TensorProduct.mapIsometry U (powerMap F V n))

@[simp] lemma wordMap_word (U : E →ₗᵢ[ℂ] E) (V : F →ₗᵢ[ℂ] F) (n : ℕ)
    (d : E) (x : Fin n → F) :
    wordMap E F U V n (word E F n d x) = word E F n (U d) (fun i => V (x i)) := by
  simp only [wordMap, word, completionIsometry_coe, TensorProduct.mapIsometry_apply,
    TensorProduct.map_tmul, LinearIsometry.coe_toLinearMap, powerMap_pure]

end PreHilbert

open PreHilbert

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorPowerCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

open UniformSpace

open scoped TensorProduct

variable (E F : PreHilbert)

def powerEquiv (U : Completion E ≃ₗᵢ[ℂ] Completion F) : ∀ n,
    Completion (PreHilbert.power E n) ≃ₗᵢ[ℂ] Completion (PreHilbert.power F n)
  | 0 => .refl ℂ _
  | n+1 => (tensor (E := E) (F := PreHilbert.power E n)).trans
      ((congr (TensorProduct.congrIsometry U (powerEquiv U n))).trans
        (tensor (E := F) (F := PreHilbert.power F n)).symm)

variable (E' F' : PreHilbert)

def wordEquiv (U : Completion E ≃ₗᵢ[ℂ] Completion E')
    (V : Completion F ≃ₗᵢ[ℂ] Completion F') (n : ℕ) :
    Completion (E ⊗[ℂ] PreHilbert.power F n) ≃ₗᵢ[ℂ]
      Completion (E' ⊗[ℂ] PreHilbert.power F' n) :=
  (tensor (E := E) (F := PreHilbert.power F n)).trans
    ((congr (TensorProduct.congrIsometry U (powerEquiv F F' V n))).trans
      (tensor (E := E') (F := PreHilbert.power F' n)).symm)

end Kadison.HilbertCompletion
end

end OAI
end


