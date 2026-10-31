-- Prove2me | solution 1 for AlgebraicPCSP.Theory.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:47:11.794462+00:00
-- url     : https://prove2.me/submissions/22e357e4-c345-4e80-8ed2-6df9c3bad6d5

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction
import Theorems.Thm_AlgebraicPCSP_Theory_theorem_4_12

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Theory
open scoped Classical

lemma proj_mem_pol {τ₁ : Type} {ar₁ : τ₁ → ℕ} {A₁ B₁ : Type}
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁) (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁)
    {k : ℕ} (i : Fin k) (σ : A₁ → B₁) (hσ : IsHom 𝔸₁ 𝔹₁ σ) :
    (fun x : Fin k → A₁ => σ (x i)) ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem k := by
  refine ⟨Fin.pos i, ?_⟩
  intro R M hM
  exact hσ R (M i) (hM i)

theorem solution {τ₁ τ₂ : Type} [Fintype τ₁] [Fintype τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ A₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂]
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁) (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁)
    (𝔸₂ : RelStruct τ₂ ar₂ A₂) (hne : ∀ R, (𝔸₂.rel R).Nonempty)
    {n : ℕ} (e : Fin n ≃ A₂) (m : τ₂ → ℕ) (eR : (R : τ₂) → Fin (m R) ≃ 𝔸₂.rel R) :
    ∃ (N : ℕ) (𝔸' : RelStruct τ₂ ar₂ (Fin N → A₁)) (𝔹' : RelStruct τ₂ ar₂ (Fin N → B₁)),
      IsPPPower N 𝔸₁ 𝔹₁ 𝔸' 𝔹' ∧
        IsRelaxation 𝔸' 𝔹' 𝔸₂ (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) := by
  rcases h₁ with ⟨σ₁, hσ₁⟩
  let h₁' : IsPromiseTemplate 𝔸₁ 𝔹₁ := ⟨σ₁, hσ₁⟩
  let F := freeStructure (Pol 𝔸₁ 𝔹₁ h₁') 𝔸₂ e m eR
  let homF : A₂ → {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁').mem n} :=
    fun a => ⟨fun x => σ₁ (x (e.symm a)), proj_mem_pol 𝔸₁ 𝔹₁ h₁' (e.symm a) σ₁ hσ₁⟩
  have hIsHomF : IsHom 𝔸₂ F homF := by
    intro R r₀ hr₀
    let j₀ : Fin (m R) := (eR R).symm ⟨r₀, hr₀⟩
    refine ⟨fun y => σ₁ (y j₀), proj_mem_pol 𝔸₁ 𝔹₁ h₁' j₀ σ₁ hσ₁, ?_⟩
    intro i
    ext x
    change σ₁ (x (e.symm (r₀ i))) = σ₁ (x (e.symm ((eR R j₀).val i)))
    have hj₀ : eR R j₀ = ⟨r₀, hr₀⟩ := Equiv.apply_symm_apply (eR R) ⟨r₀, hr₀⟩
    rw [hj₀]
  haveI : Nonempty {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁').mem n} := ⟨homF (Classical.arbitrary A₂)⟩
  have h₂ : IsPromiseTemplate 𝔸₂ F := ⟨homF, hIsHomF⟩
  have htfae := (theorem_4_12 har₁ har₂ 𝔸₁ 𝔹₁ 𝔸₂ F hne h₁' h₂ e m eR).out 3 4
  exact htfae.mp ⟨id, fun _ _ ht => ht⟩
