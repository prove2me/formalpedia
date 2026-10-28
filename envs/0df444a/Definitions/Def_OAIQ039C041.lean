-- Prove2me | Definitions.Def_OAIQ039C041
-- name    : OAIQ039C041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:23:21.0062+00:00
-- url     : https://prove2.me/theorems/2f842443-c4db-4220-8e6b-97cd22612890
-- title:
--   Definitions bundle OAIQ039C041 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 2 definitions and 4 theorems. The definitions and types are `OAI.Kadison.VectorGNS.compression`, `OAI.Kadison.coefficient`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CoefficientForm`, `Commutator_CoefficientForm2`, `Commutator_GNSVectorEmbedding`, `Commutator_ProjectionStrong`.
--
--   **Imports.** It imports the bundles `OAIQ039C016`, `OAIQ039C024`, `OAIQ039C026` and `OAIQ039C029` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C052`; the proofs of `OAI.Kadison.FreeBlocks.normal_free_original_bound`, `OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings` and `OAI.Kadison.PositiveWOT.threshold_exhaustion`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C016
import Definitions.Def_OAIQ039C024
import Definitions.Def_OAIQ039C026
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_CoefficientForm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma word_update_smul (E F : PreHilbert) (n : ℕ) (d : E) (v : Fin n → F)
    (i : Fin n) (c : ℂ) (x : F) :
    word E F n d (update v i (c • x)) = c • word E F n d (update v i x) := by
  simp only [word, pure_update_smul, TensorProduct.tmul_smul, Completion.coe_smul]

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CoefficientForm2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

open PreHilbert Function

variable (E F : PreHilbert) (k l : ℕ)

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [StarAddMonoid M] [StarModule ℂ M]

def coefficient (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M) : ℂ :=
  inner ℂ (word E F l (v₀ (star (A none))) (fun j => v₁ (star (A (some (.inr j))))))
    (Y (word E F k Ω (fun i => v₁ (A (some (.inl i))))))

variable [DecidableEq (Option (Fin k ⊕ Fin l))]

omit [StarModule ℂ M] in
lemma coefficient_update_inl
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M)
    (i : Fin k) (x : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A (some (.inl i)) x) =
      inner ℂ (word E F l (v₀ (star (A none))) (fun j => v₁ (star (A (some (.inr j))))))
        (Y (word E F k Ω (update (fun a => v₁ (A (some (.inl a)))) i (v₁ x)))) := by
  have he : (fun a => v₁ (update A (some (.inl i)) x (some (.inl a)))) =
      update (fun a => v₁ (A (some (.inl a)))) i (v₁ x) := by
    funext a
    by_cases ha : a = i <;> simp [ha]
  have hn : (none : Option (Fin k ⊕ Fin l)) ≠ some (.inl i) := by simp
  have hr : ∀ j : Fin l, (some (.inr j) : Option (Fin k ⊕ Fin l)) ≠ some (.inl i) := by simp
  simp only [coefficient, update_of_ne hn, update_of_ne (hr _), he]

omit [StarModule ℂ M] in
lemma coefficient_update_inr
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M)
    (j : Fin l) (x : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A (some (.inr j)) x) =
      inner ℂ (word E F l (v₀ (star (A none)))
        (update (fun b => v₁ (star (A (some (.inr b))))) j (v₁ (star x))))
        (Y (word E F k Ω (fun a => v₁ (A (some (.inl a)))))) := by
  have he : (fun b => v₁ (star (update A (some (.inr j)) x (some (.inr b))))) =
      update (fun b => v₁ (star (A (some (.inr b))))) j (v₁ (star x)) := by
    funext b
    by_cases hb : b = j <;> simp [hb]
  have hn : (none : Option (Fin k ⊕ Fin l)) ≠ some (.inr j) := by simp
  have hr : ∀ i : Fin k, (some (.inl i) : Option (Fin k ⊕ Fin l)) ≠ some (.inr j) := by simp
  simp only [coefficient, update_of_ne hn, update_of_ne (hr _), he]

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

def compression (T : H →L[ℂ] H) : τ.GNS →L[ℂ] τ.GNS :=
  FreeCorner.compress (embedding τ φ ξ hτ) T

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionStrong
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionChains

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_strong_sup (M : VonNeumannAlgebra H)
    (P : ℕ → H →L[ℂ] H) (hp : ∀ n,IsStarProjection (P n))
    (hmem : ∀ n,P n∈M) (hmono : Monotone P) :
    ∃ W : H →L[ℂ] H,W∈M ∧ IsStarProjection W ∧ (∀ n,P n≤W) ∧
      (∀ x,Tendsto (fun n => P n x) atTop (𝓝 (W x))) ∧
      ∀ Q : H →L[ℂ] H,IsStarProjection Q → (∀ n,P n≤Q) → W≤Q := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨W,hW,hPW,hlim,hle⟩ := monotone_ultralimit ω hω P hp hmono
  have hs (x y : H) : Tendsto (fun n => inner ℂ (P n x) y) (ω : Filter ℕ)
      (𝓝 (inner ℂ (W x) y)) := by
    have hh := tendsto_iff_forall_inner_apply_tendsto.mp hlim x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using hh.star
  refine ⟨W,WeakOperatorLimit.mem_vonNeumann hs M (Filter.Eventually.of_forall hmem),hW,hPW,?_,hle⟩
  intro x
  have hdiff (n : ℕ) : IsStarProjection (W-P n) :=
    (hp n).sub_of_mul_eq_left hW ((hp n).le_iff_mul_eq_left hW |>.mp (hPW n))
  have hnorm : Tendsto (fun n => ‖(W-P n) x‖^2) (ω : Filter ℕ) (𝓝 0) := by
    simp_rw [projection_norm_sq (hdiff _)]
    simp only [_root_.sub_apply,inner_sub_left,Complex.sub_re]
    simpa only [sub_self,Function.comp_apply] using (tendsto_const_nhds (x := (inner ℂ (W x) x).re)).sub (Complex.continuous_re.tendsto _ |>.comp (hs x x))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (hnorm.eventually_lt_const (sq_pos_of_pos hε)).exists
  refine ⟨N,?_⟩
  intro n hn
  have hle' : W-P n≤W-P N := sub_le_sub_left (hmono hn) W
  have hnm := projection_norm_mono (hdiff n) (hdiff N) hle' x
  have hlt : ‖(W-P N) x‖<ε := by nlinarith [norm_nonneg ((W-P N) x)]
  rw [dist_eq_norm,←norm_neg,neg_sub]
  exact hnm.trans_lt hlt

end Kadison.ProjectionChains

end

end
end

end OAI
end


