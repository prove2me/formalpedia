-- Prove2me | solution 1 for AlgebraicPCSP.Theory.corollary_4_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:47:45.360683+00:00
-- url     : https://prove2.me/submissions/e3d610d9-54bb-47c4-9e62-2e920f18c55b

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction
import Theorems.Thm_AlgebraicPCSP_Theory_lemma_4_8_pp_power
import Theorems.Thm_AlgebraicPCSP_Theory_lemma_4_8_relaxation

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Theory

lemma isMinionHom_id {A B : Type} (M : Minion A B) :
    IsMinionHom M M (fun _ f => f) := by
  intro m n π g hg
  rfl

lemma isMinionHom_comp {A₁ B₁ A₂ B₂ A₃ B₃ : Type}
    {M₁ : Minion A₁ B₁} {M₂ : Minion A₂ B₂} {M₃ : Minion A₃ B₃}
    {ξ₁ : (n : ℕ) → {f // f ∈ M₁.mem n} → {f // f ∈ M₂.mem n}}
    {ξ₂ : (n : ℕ) → {f // f ∈ M₂.mem n} → {f // f ∈ M₃.mem n}}
    (h₁ : IsMinionHom M₁ M₂ ξ₁) (h₂ : IsMinionHom M₂ M₃ ξ₂) :
    IsMinionHom M₁ M₃ (fun n f => ξ₂ n (ξ₁ n f)) := by
  intro m n π g hg
  have hsub : (⟨fun x => g (x ∘ π), M₁.minor_mem π g hg⟩ : {f // f ∈ M₁.mem n}) =
      ⟨fun x => g (x ∘ π), M₁.minor_mem π g hg⟩ := rfl
  have h1 := h₁ π g hg
  have hsub2 : ξ₁ n ⟨fun x => g (x ∘ π), M₁.minor_mem π g hg⟩ =
      ⟨fun x => (ξ₁ m ⟨g, hg⟩).val (x ∘ π), M₂.minor_mem π (ξ₁ m ⟨g, hg⟩).val (ξ₁ m ⟨g, hg⟩).property⟩ :=
    Subtype.ext h1
  dsimp only
  rw [hsub2]
  exact h₂ π (ξ₁ m ⟨g, hg⟩).val (ξ₁ m ⟨g, hg⟩).property

lemma sum_elim_comp {α β γ δ : Type*} (f : γ → δ) (a : α → γ) (b : β → γ) (x : α ⊕ β) :
    Sum.elim (f ∘ a) (f ∘ b) x = f (Sum.elim a b x) := by
  cases x <;> rfl

lemma isPromiseTemplate_of_isPPPower {τ₁ τ₂ : Type} {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ}
    {A B : Type} (n : ℕ) (𝔸₁ : RelStruct τ₁ ar₁ A) (𝔹₁ : RelStruct τ₁ ar₁ B)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B))
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (hpow : IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    IsPromiseTemplate 𝔸₂ 𝔹₂ := by
  rcases h₁ with ⟨σ, hσ⟩
  refine ⟨fun x i => σ (x i), ?_⟩
  intro R t ht
  rcases hpow R with ⟨Ψ, hΨA, hΨB⟩
  rw [hΨB]
  rcases (hΨA t).mp ht with ⟨b, hatom, heqn⟩
  refine ⟨σ ∘ b, ?_, ?_⟩
  · intro a
    have hcomp : (fun j => Sum.elim (fun p : Fin (ar₂ R) × Fin n => ((fun x i => σ (x i)) ∘ t) p.1 p.2) (σ ∘ b)
        (Ψ.atomArgs a j)) =
      σ ∘ (fun j => Sum.elim (fun p : Fin (ar₂ R) × Fin n => t p.1 p.2) b (Ψ.atomArgs a j)) := by
      ext j
      exact sum_elim_comp σ (fun p : Fin (ar₂ R) × Fin n => t p.1 p.2) b (Ψ.atomArgs a j)
    rw [hcomp]
    exact hσ (Ψ.atomSym a) _ (hatom a)
  · intro q
    have h1 := sum_elim_comp σ (fun p : Fin (ar₂ R) × Fin n => t p.1 p.2) b (Ψ.eqns q).1
    have h2 := sum_elim_comp σ (fun p : Fin (ar₂ R) × Fin n => t p.1 p.2) b (Ψ.eqns q).2
    change Sum.elim (σ ∘ fun p : Fin (ar₂ R) × Fin n => t p.1 p.2) (σ ∘ b) (Ψ.eqns q).1 =
      Sum.elim (σ ∘ fun p : Fin (ar₂ R) × Fin n => t p.1 p.2) (σ ∘ b) (Ψ.eqns q).2
    rw [h1, h2, heqn q]

lemma ppConstructible_ind (T T' : Template) (hT : IsPromiseTemplate T.𝔸 T.𝔹)
    (hc : PPConstructible T T') :
    IsPromiseTemplate T'.𝔸 T'.𝔹 ∧
      ∀ hT' : IsPromiseTemplate T'.𝔸 T'.𝔹, ∃ ξ, IsMinionHom (Pol T.𝔸 T.𝔹 hT) (Pol T'.𝔸 T'.𝔹 hT') ξ := by
  induction hc with
  | refl =>
    exact ⟨hT, fun _ => ⟨fun _ f => f, isMinionHom_id _⟩⟩
  | @power T₁ hT₁ n τ'' _ ar'' har'' 𝔸'' 𝔹'' hpow ih =>
    rcases ih with ⟨h₁, ih_hom⟩
    rcases ih_hom h₁ with ⟨ξ₁, hξ₁⟩
    have h₂ : IsPromiseTemplate 𝔸'' 𝔹'' :=
      isPromiseTemplate_of_isPPPower n T₁.𝔸 T₁.𝔹 𝔸'' 𝔹'' h₁ hpow
    refine ⟨h₂, fun h₂' => ?_⟩
    rcases lemma_4_8_pp_power T₁.ar_pos har'' n T₁.𝔸 T₁.𝔹 𝔸'' 𝔹'' h₁ h₂' hpow with ⟨ξ₂, hξ₂⟩
    exact ⟨fun m f => ξ₂ m (ξ₁ m f), isMinionHom_comp hξ₁ hξ₂⟩
  | @relax T₁ hT₁ A'' B'' _ _ _ _ _ _ 𝔸'' 𝔹'' htemp hrel ih =>
    rcases ih with ⟨h₁, ih_hom⟩
    rcases ih_hom h₁ with ⟨ξ₁, hξ₁⟩
    refine ⟨htemp, fun h₂' => ?_⟩
    rcases lemma_4_8_relaxation T₁.ar_pos T₁.𝔸 T₁.𝔹 𝔸'' 𝔹'' h₁ h₂' hrel with ⟨ξ₂, hξ₂⟩
    exact ⟨fun m f => ξ₂ m (ξ₁ m f), isMinionHom_comp hξ₁ hξ₂⟩

theorem solution (T T' : Template) (hT : IsPromiseTemplate T.𝔸 T.𝔹)
    (hT' : IsPromiseTemplate T'.𝔸 T'.𝔹) (hc : PPConstructible T T') :
    ∃ ξ, IsMinionHom (Pol T.𝔸 T.𝔹 hT) (Pol T'.𝔸 T'.𝔹 hT') ξ :=
  (ppConstructible_ind T T' hT hc).2 hT'
