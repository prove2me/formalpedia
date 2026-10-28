-- Prove2me | solution 1 for AlgebraicPCSP.Theory.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:59:59.935654+00:00
-- url     : https://prove2.me/submissions/1bba2548-b17b-46f6-a26e-1700945851ff

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.Theory in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B I : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (𝕀 : RelStruct τ ar I)
    {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ) (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) :
    ((∃ h : I → A, IsHom 𝕀 𝔸 h) → IsTrivial (sigmaCondition 𝔸 𝕀 e m eR)) ∧
    (SatisfiedIn (sigmaCondition 𝔸 𝕀 e m eR) (polFamily 𝔸 𝔹) → ∃ h : I → B, IsHom 𝕀 𝔹 h) := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨fun u x => x (e.symm (h u)),
      fun C x => x ((eR C.1).symm ⟨h ∘ C.2.val, hh C.1 C.2.val C.2.prop⟩),
      fun u => ⟨_, rfl⟩, fun C => ⟨_, rfl⟩, ?_⟩
    rintro ⟨⟨R, t⟩, j⟩
    funext x
    change x (e.symm (h (t.val j))) =
      x (e.symm (((eR R) ((eR R).symm ⟨h ∘ t.val, hh R t.val t.prop⟩)).val j))
    rw [Equiv.apply_symm_apply]
    rfl
  · rintro ⟨ζU, ζV, hU, hV, heq⟩
    refine ⟨fun i => ζU i e, ?_⟩
    intro R t ht
    have hpol := (hV ⟨R, ⟨t, ht⟩⟩).2 R (fun jj => (eR R jj).val) (fun jj => (eR R jj).prop)
    convert hpol using 1
    funext c
    have := congrFun (heq ⟨⟨R, ⟨t, ht⟩⟩, c⟩) e
    show ζU (t c) e = ζV ⟨R, ⟨t, ht⟩⟩ (fun l => (eR R l).val c)
    refine this.trans ?_
    show ζV ⟨R, ⟨t, ht⟩⟩ (⇑e ∘ fun j => e.symm ((eR R j).val c)) = _
    congr 1
    funext j
    simp
