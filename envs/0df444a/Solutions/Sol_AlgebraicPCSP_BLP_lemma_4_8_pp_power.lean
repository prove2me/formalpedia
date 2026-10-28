-- Prove2me | solution 1 for AlgebraicPCSP.BLP.lemma_4_8_pp_power
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:03:11.247419+00:00
-- url     : https://prove2.me/submissions/34f5d34a-76a8-425c-b508-30b10800a7e4

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction

open AlgebraicPCSP.BLP
open PCSPBLPAff.Symmetric
namespace Aux_APCSP_48
open PCSPBLPAff.Symmetric

theorem pol_lift {τ₁ τ₂ : Type} {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} {A₁ B₁ : Type} (n : ℕ)
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A₁)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B₁))
    (hpow : AlgebraicPCSP.Theory.IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) {N : ℕ}
    (f : (Fin N → A₁) → B₁) (hf : IsPolymorphism 𝔸₁ 𝔹₁ f) :
    IsPolymorphism 𝔸₂ 𝔹₂ (fun (x : Fin N → Fin n → A₁) (k : Fin n) => f (fun l => x l k)) := by
  intro R M hM
  obtain ⟨Ψ, hA, hB⟩ := hpow R
  have hh : ∀ l, Ψ.Holds 𝔸₁ (fun p => M l p.1 p.2) := fun l => (hA (M l)).mp (hM l)
  choose b hbat hbeq using hh
  rw [hB]
  refine ⟨fun y => f (fun l => b l y), ?_, ?_⟩
  · intro t
    have e : (fun j => Sum.elim (fun p : Fin (ar₂ R) × Fin n => f (fun l => M l p.1 p.2))
        (fun y => f (fun l => b l y)) (Ψ.atomArgs t j))
        = fun j => f (fun l => Sum.elim (fun p : Fin (ar₂ R) × Fin n => M l p.1 p.2) (b l)
            (Ψ.atomArgs t j)) := by
      funext j
      cases Ψ.atomArgs t j <;> rfl
    rw [e]
    exact hf _ (fun l j => Sum.elim (fun p : Fin (ar₂ R) × Fin n => M l p.1 p.2) (b l)
      (Ψ.atomArgs t j)) (fun l => hbat l t)
  · intro q
    have e : ∀ z : Fin (ar₂ R) × Fin n ⊕ Ψ.Y,
        Sum.elim (fun p : Fin (ar₂ R) × Fin n => f (fun l => M l p.1 p.2))
          (fun y => f (fun l => b l y)) z
        = f (fun l => Sum.elim (fun p : Fin (ar₂ R) × Fin n => M l p.1 p.2) (b l) z) := by
      intro z; cases z <;> rfl
    rw [e, e]
    congr 1
    funext l
    exact hbeq l q

end Aux_APCSP_48

theorem solution {τ₁ τ₂ : Type} [Finite τ₁] [Finite τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ : Type} (n : ℕ)
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A₁)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B₁))
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    (hpow : AlgebraicPCSP.Theory.IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom (AlgebraicPCSP.Theory.Pol 𝔸₁ 𝔹₁ h₁) (AlgebraicPCSP.Theory.Pol 𝔸₂ 𝔹₂ h₂) ξ := by
  refine ⟨fun N f => ⟨fun x k => f.1 (fun l => x l k),
    f.2.1, Aux_APCSP_48.pol_lift n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂ hpow f.1 f.2.2⟩, ?_⟩
  intro m N π g hg
  rfl
