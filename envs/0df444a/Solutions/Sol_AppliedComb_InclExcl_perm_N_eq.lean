-- Prove2me | solution 1 for AppliedComb.InclExcl.perm_N_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:22:58.953093+00:00
-- url     : https://prove2.me/submissions/9914c654-051b-444f-bbd6-3be8775e7be6

import Mathlib
import Definitions.Def_AppliedComb_InclExcl_N
import Definitions.Def_AppliedComb_InclExcl_properties

open AppliedComb.InclExcl in
theorem perm_N_eq_aux_50f485fa (n : ℕ) (S : Finset (Fin n)) :
    N (FixesPoint n) S = (n - S.card).factorial := by
  have e : {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, FixesPoint n i σ} ≃
      Equiv.Perm {a : Fin n // a ∉ S} :=
    (Equiv.subtypeEquivRight (fun σ => by
      simp only [FixesPoint, not_not])).trans
      (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ S)).symm
  have h1 : N (FixesPoint n) S =
      Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, FixesPoint n i σ} := by
    unfold N
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

open AppliedComb.InclExcl in
theorem solution (n : ℕ) :
    (∀ S T : Finset (Fin n), S.card = T.card →
      N (FixesPoint n) S = N (FixesPoint n) T) ∧
    ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k →
      N (FixesPoint n) S = (n - k).factorial := by
  refine ⟨fun S T h => ?_, fun k S h => ?_⟩
  · rw [perm_N_eq_aux_50f485fa, perm_N_eq_aux_50f485fa, h]
  · rw [perm_N_eq_aux_50f485fa, h]
