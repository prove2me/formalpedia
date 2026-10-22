-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.section_8_4_pigeonhole
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:48:59.806318+00:00
-- url     : https://prove2.me/submissions/b302d87e-6804-418f-8e76-afe766c9087f

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
set_option autoImplicit false
open AlgebraicPCSP.OneInThree

theorem solution {D : Type} [Fintype D] [DecidableEq D] (f : Fin 2 → D)
    {p : ℕ} (hp : p.Prime) (hpD : 60 * Fintype.card D < p) (s : (Fin p → D) → D) :
    ∃ l₁ l₂ : ℕ, (p : ℚ) / 3 - 2 * (Fintype.card D : ℚ) < l₁ ∧ l₁ < l₂ ∧
      (l₂ : ℚ) < (p : ℚ) / 3 ∧
      s (fun j => f (prefixOnes p l₁ j)) = s (fun j => f (prefixOnes p l₂ j)) := by
  have hDpos : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨f 0⟩
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).mp hd with h3 | h3
    · omega
    · omega
  set c := Fintype.card D with hc
  set m := (p - 1) / 3 with hm
  let F : Fin (2 * c) → D := fun k => s (fun j => f (prefixOnes p (m - k.val) j))
  have hcard : Fintype.card D < Fintype.card (Fin (2 * c)) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨a, b, hab, hF⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  have key : ∀ a b : Fin (2 * c), a.val < b.val → F a = F b →
      ∃ l₁ l₂ : ℕ, (p : ℚ) / 3 - 2 * (c : ℚ) < l₁ ∧ l₁ < l₂ ∧
      (l₂ : ℚ) < (p : ℚ) / 3 ∧
      s (fun j => f (prefixOnes p l₁ j)) = s (fun j => f (prefixOnes p l₂ j)) := by
    intro a b hab hF
    have hb := b.2
    refine ⟨m - b.val, m - a.val, ?_, ?_, ?_, hF.symm⟩
    · have h1 : p < 3 * (m - b.val) + 6 * c := by omega
      have h2 : (p : ℚ) < 3 * ((m - b.val : ℕ) : ℚ) + 6 * (c : ℚ) := by exact_mod_cast h1
      linarith
    · omega
    · have h1 : 3 * (m - a.val) < p := by omega
      have h3 : (((m - a.val : ℕ)) : ℚ) < (p : ℚ) / 3 := by
        have : (3 : ℚ) * ((m - a.val : ℕ) : ℚ) < p := by exact_mod_cast h1
        linarith
      exact h3
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h hF
  · exact key b a h hF.symm
