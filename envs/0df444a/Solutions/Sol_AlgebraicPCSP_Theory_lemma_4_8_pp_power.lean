-- Prove2me | solution 1 for AlgebraicPCSP.Theory.lemma_4_8_pp_power
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:02:51.171754+00:00
-- url     : https://prove2.me/submissions/f9e74e72-7c93-4eda-ad74-d9a21cecfd6f

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.Theory in
theorem solution {τ₁ τ₂ : Type} [Fintype τ₁] [Fintype τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁] (n : ℕ)
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A₁)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B₁))
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hpow : IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, IsMinionHom (Pol 𝔸₁ 𝔹₁ h₁) (Pol 𝔸₂ 𝔹₂ h₂) ξ := by
  have key : ∀ (L : ℕ) (f : {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem L}),
      (fun x : Fin L → Fin n → A₁ => fun k : Fin n => f.1 (fun l => x l k)) ∈
        (Pol 𝔸₂ 𝔹₂ h₂).mem L := by
    intro L f
    have hf : 0 < L ∧ IsPolymorphism 𝔸₁ 𝔹₁ f.1 := f.2
    change 0 < L ∧ IsPolymorphism 𝔸₂ 𝔹₂
      (fun x : Fin L → Fin n → A₁ => fun k : Fin n => f.1 (fun l => x l k))
    refine ⟨hf.1, ?_⟩
    intro R M hM
    obtain ⟨Ψ, hΨA, hΨB⟩ := hpow R
    choose b hb using fun l => (hΨA (M l)).mp (hM l)
    rw [hΨB]
    have hk : ∀ z : Fin (ar₂ R) × Fin n ⊕ Ψ.Y,
        Sum.elim (fun p => (fun c => (fun k : Fin n => f.1 (fun l => M l c k))) p.1 p.2)
          (fun y => f.1 (fun l => b l y)) z =
        f.1 (fun l => Sum.elim (fun p => M l p.1 p.2) (b l) z) := by
      rintro (z | z) <;> rfl
    refine ⟨fun y => f.1 (fun l => b l y), fun t => ?_, fun q => ?_⟩
    · convert hf.2 (Ψ.atomSym t) (fun l j => Sum.elim (fun p => M l p.1 p.2) (b l) (Ψ.atomArgs t j))
        (fun l => (hb l).1 t) using 1
      funext j
      exact hk _
    · rw [hk, hk]
      exact congrArg f.1 (funext fun l => (hb l).2 q)
  refine ⟨fun L f => ⟨fun x k => f.1 (fun l => x l k), key L f⟩, ?_⟩
  intro m n' π g hg
  rfl
