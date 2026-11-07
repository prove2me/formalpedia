-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:58.826977+00:00
-- url     : https://prove2.me/submissions/a738ddf9-ac0e-4c27-be71-92c49ebb0e75

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} : HasDegreeLE f 0 ↔ ∃ a : ℝ, ∀ x, f x = a := by
  constructor
  · rintro ⟨c, hc, hf⟩
    refine ⟨c ∅, fun x => ?_⟩
    rw [hf x, Finset.sum_eq_single (∅ : Finset ι)]
    · simp [chi]
    · intro S _ hS
      rw [hc S (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rintro ⟨a, ha⟩
    refine ⟨fun S => if S = ∅ then a else 0, ?_, fun x => ?_⟩
    · intro S hS
      have hne : S ≠ ∅ := by
        rintro rfl
        simp at hS
      simp [hne]
    · rw [ha x, Finset.sum_eq_single (∅ : Finset ι)]
      · simp [chi]
      · intro S _ hS
        simp [hS]
      · intro h
        exact absurd (Finset.mem_univ _) h
end AaronsonAmbainis.Bridge
