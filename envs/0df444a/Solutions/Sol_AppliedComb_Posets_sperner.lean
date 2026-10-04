-- Prove2me | solution 1 for AppliedComb.Posets.sperner
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:42:10.626258+00:00
-- url     : https://prove2.me/submissions/83623c7a-d982-4179-873e-adcbe2540ad0

import Mathlib
import Definitions.Def_AppliedComb_Posets_width

open AppliedComb.Posets in
theorem solution (t : ℕ) (ht : 1 ≤ t) :
    width (Finset (Fin t)) = Nat.choose t (t / 2) := by
  classical
  unfold width
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    rw [Finset.mem_filter] at hA
    have h := IsAntichain.sperner (𝒜 := A) hA.2
    simpa using h
  · have hanti : IsAntichain (· ≤ ·)
        ((Finset.powersetCard (t / 2) (Finset.univ : Finset (Fin t)) : Finset (Finset (Fin t))) :
          Set (Finset (Fin t))) := by
      have := (Set.sized_powersetCard (Finset.univ : Finset (Fin t)) (t / 2)).isAntichain
      exact this
    have hmem : Finset.powersetCard (t / 2) (Finset.univ : Finset (Fin t)) ∈
        (Finset.univ : Finset (Finset (Finset (Fin t)))).filter
          (fun A : Finset (Finset (Fin t)) => IsAntichain (· ≤ ·) (A : Set (Finset (Fin t)))) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hanti⟩
    have := Finset.le_sup (f := Finset.card) hmem
    simpa [Finset.card_powersetCard] using this
