-- Prove2me | solution 1 for AlgebraicPCSP.BLP.lemma_4_8_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:56:02.411032+00:00
-- url     : https://prove2.me/submissions/d003e896-79dd-4e8d-a3c0-1eb240de6fdd

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.BLP in
theorem solution {τ : Type} [Finite τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A₁ B₁ A₂ B₂ : Type}
    (𝔸₁ : RelStruct τ ar A₁) (𝔹₁ : RelStruct τ ar B₁)
    (𝔸₂ : RelStruct τ ar A₂) (𝔹₂ : RelStruct τ ar B₂)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hrel : AlgebraicPCSP.Theory.IsRelaxation 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom (AlgebraicPCSP.Theory.Pol 𝔸₁ 𝔹₁ h₁) (AlgebraicPCSP.Theory.Pol 𝔸₂ 𝔹₂ h₂) ξ := by
  obtain ⟨⟨hA, hAh⟩, ⟨hB, hBh⟩⟩ := hrel
  refine ⟨fun n f => ⟨fun x => hB (f.val (hA ∘ x)), f.2.1, ?_⟩, ?_⟩
  · intro R M hM
    exact hBh R _ (f.2.2 R (fun l => hA ∘ M l) (fun l => hAh R _ (hM l)))
  · intro m n π g hg
    rfl
