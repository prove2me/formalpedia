-- Prove2me | solution 1 for A166944Research.a166944_event_dvd_next_horizon
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:18:44.549423+00:00
-- url     : https://prove2.me/submissions/6e9778ef-6c9a-4c46-8e6d-5bb1c03b1c79

import Definitions.Def_a166944_moving_horizon

namespace A166944Research

theorem step_facts_aux {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    3 ≤ r ∧ 2 * r < a r ∧
    (r % 2 = 0 → a r = a (r - 1) + Nat.gcd r (a (r - 1))) ∧
    (r % 2 = 1 → a r = a (r - 1) + Nat.gcd (r - 2) (a (r - 1))) := by
  obtain ⟨⟨hs2, _, _⟩, hsr, _, _, _, _, _, _, ⟨_, hDr, hrC'⟩⟩ := hstep
  have h3 : 3 ≤ r := by omega
  refine ⟨h3, ?_, ?_, ?_⟩
  · unfold D at hDr; omega
  · intro hr
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
    rw [a]
    simp only [show (n + 2) % 2 = 0 from hr, if_true, show n + 2 - 1 = n + 1 by omega]
  · intro hr
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
    rw [a]
    have : ¬ (n + 2) % 2 = 0 := by omega
    simp only [this, if_false, show n + 2 - 1 = n + 1 by omega]

theorem sol_even_aux {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 0) :
    d r ∣ C' - r ∧ d r ∣ C' := by
  obtain ⟨h3, hlt, he, _⟩ := step_facts_aux hstep
  have hC' : C' = D r := hstep.2.2.2.2.2.2.1
  have hrec := he hr
  have hd : d r = Nat.gcd r (a (r - 1)) := by unfold d; omega
  have h1 : d r ∣ r := hd ▸ Nat.gcd_dvd_left _ _
  have h2 : d r ∣ a r := by
    rw [hrec]; exact Nat.dvd_add (hd ▸ Nat.gcd_dvd_right _ _) (hd ▸ dvd_rfl)
  have hD : C' = a r - r := by rw [hC']; rfl
  refine ⟨?_, ?_⟩
  · rw [hD]; exact Nat.dvd_sub (Nat.dvd_sub h2 h1) h1
  · rw [hD]; exact Nat.dvd_sub h2 h1

theorem sol_odd_aux {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hr : r % 2 = 1) :
    d r ∣ C' - r + 4 ∧ d r ∣ C' + 2 := by
  obtain ⟨h3, hlt, _, ho⟩ := step_facts_aux hstep
  have hC' : C' = D r := hstep.2.2.2.2.2.2.1
  have hrec := ho hr
  have hd : d r = Nat.gcd (r - 2) (a (r - 1)) := by unfold d; omega
  have h1 : d r ∣ r - 2 := hd ▸ Nat.gcd_dvd_left _ _
  have h2 : d r ∣ a r := by
    rw [hrec]; exact Nat.dvd_add (hd ▸ Nat.gcd_dvd_right _ _) (hd ▸ dvd_rfl)
  have hD : C' = a r - r := by rw [hC']; rfl
  refine ⟨?_, ?_⟩
  · have : C' - r + 4 = a r - (r - 2) - (r - 2) := by omega
    rw [this]; exact Nat.dvd_sub (Nat.dvd_sub h2 h1) h1
  · have : C' + 2 = a r - (r - 2) := by omega
    rw [this]; exact Nat.dvd_sub h2 h1

end A166944Research

open A166944Research

theorem solution {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 → d r ∣ C') ∧ (r % 2 = 1 → d r ∣ C' + 2) :=
  ⟨fun hr => (sol_even_aux hstep hr).2, fun hr => (sol_odd_aux hstep hr).2⟩
