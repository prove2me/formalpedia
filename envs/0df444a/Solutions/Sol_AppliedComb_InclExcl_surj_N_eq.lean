-- Prove2me | solution 1 for AppliedComb.InclExcl.surj_N_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:37:24.472973+00:00
-- url     : https://prove2.me/submissions/a8926b72-4fe9-4cce-9e3f-46f0eb6d1966

import Mathlib
import Definitions.Def_AppliedComb_InclExcl_N
import Definitions.Def_AppliedComb_InclExcl_properties

open AppliedComb.InclExcl in
theorem surj_N_eq_aux_30819acb (n m : ℕ) (S : Finset (Fin m)) :
    N (NotInRange n m) S = (m - S.card) ^ n := by
  have h : (Finset.univ.filter (fun f : Fin n → Fin m => ∀ i ∈ S, NotInRange n m i f)) =
      Fintype.piFinset (fun _ : Fin n => Sᶜ) := by
    ext f
    rw [Finset.mem_filter_univ, Fintype.mem_piFinset]
    simp only [Finset.mem_compl, NotInRange]
    constructor
    · intro hf j hj
      exact hf _ hj j rfl
    · intro hf i hi j hji
      exact hf j (hji ▸ hi)
  unfold N
  rw [h, Fintype.card_piFinset]
  simp [Finset.card_compl]

open AppliedComb.InclExcl in
theorem solution (n m : ℕ) :
    (∀ S T : Finset (Fin m), S.card = T.card →
      N (NotInRange n m) S = N (NotInRange n m) T) ∧
    ∀ (k : ℕ) (S : Finset (Fin m)), S.card = k → N (NotInRange n m) S = (m - k) ^ n := by
  refine ⟨fun S T hST => ?_, fun k S hk => ?_⟩
  · rw [surj_N_eq_aux_30819acb, surj_N_eq_aux_30819acb, hST]
  · rw [surj_N_eq_aux_30819acb, hk]
