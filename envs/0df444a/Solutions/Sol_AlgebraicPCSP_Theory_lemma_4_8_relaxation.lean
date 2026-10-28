-- Prove2me | solution 1 for AlgebraicPCSP.Theory.lemma_4_8_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:35:46.694879+00:00
-- url     : https://prove2.me/submissions/7d4a18b1-c121-4392-897a-a9d89d3ac631

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.Theory in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A₁ B₁ A₂ B₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂] [Fintype B₂] [DecidableEq B₂] [Nonempty B₂]
    (𝔸₁ : RelStruct τ ar A₁) (𝔹₁ : RelStruct τ ar B₁)
    (𝔸₂ : RelStruct τ ar A₂) (𝔹₂ : RelStruct τ ar B₂)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hrel : IsRelaxation 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, IsMinionHom (Pol 𝔸₁ 𝔹₁ h₁) (Pol 𝔸₂ 𝔹₂ h₂) ξ := by
  obtain ⟨⟨hA, hhA⟩, ⟨hB, hhB⟩⟩ := hrel
  have key : ∀ (n : ℕ) (f : {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem n}),
      (fun x : Fin n → A₂ => hB (f.1 (hA ∘ x))) ∈ (Pol 𝔸₂ 𝔹₂ h₂).mem n := by
    intro n f
    have hf : 0 < n ∧ IsPolymorphism 𝔸₁ 𝔹₁ f.1 := f.2
    change 0 < n ∧ IsPolymorphism 𝔸₂ 𝔹₂ (fun x : Fin n → A₂ => hB (f.1 (hA ∘ x)))
    refine ⟨hf.1, ?_⟩
    intro R M hM
    exact hhB R _ (hf.2 R (fun l => hA ∘ M l) (fun l => hhA R _ (hM l)))
  refine ⟨fun n f => ⟨fun x => hB (f.1 (hA ∘ x)), key n f⟩, ?_⟩
  intro m n π g hg
  rfl
