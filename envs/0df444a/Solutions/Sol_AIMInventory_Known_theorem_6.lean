-- Prove2me | solution 1 for AIMInventory.Known.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:24:03.79589+00:00
-- url     : https://prove2.me/submissions/be323b40-3c7d-441b-a3ba-5cc3e1a4c5d7

import Mathlib
import Definitions.Def_AIMInventory_Known_AIM
import Definitions.Def_AIMInventory_Known_Queue
open AIMInventory.Known
set_option autoImplicit false

theorem solution (h b γ ybar ρ yhat1 : ℝ) (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ)
    (hybar : 0 < ybar) (hρ : 0 < ρ) (hyhat1 : yhat1 ∈ Set.Icc 0 ybar)
    (hγρ : γ ≤ ρ * max b h / (h * ybar))
    (d : CappedBaseStock.DemandPath) (t : ℕ) (ht : 1 ≤ t) :
    aimLevel .nonPerishable ybar γ b h yhat1 d t - aimTarget .nonPerishable ybar γ b h yhat1 d t
      ≤ auxQueue ρ d t := by
  have hm : 0 < max b h := lt_of_lt_of_le hh (le_max_right _ _)
  have hscale : γ * ybar * h ≤ ρ * max b h := by
    have := (le_div_iff₀ (mul_pos hh hybar)).mp hγρ
    nlinarith
  have hproj : ∀ x, 0 ≤ projInterval ybar x ∧ projInterval ybar x ≤ ybar := by
    intro x
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) hybar.le⟩
  have hstep : ∀ n : ℕ, 1 ≤ n → 0 ≤ stepSize γ ybar b h n ∧
      stepSize γ ybar b h n * h ≤ ρ / Real.sqrt n := by
    intro n hn
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
    constructor
    · exact div_nonneg (mul_pos hγ hybar).le (mul_pos hm hs).le
    · unfold stepSize
      apply (le_div_iff₀ hs).mpr
      field_simp
      nlinarith
  have hall : ∀ n : ℕ,
      0 ≤ (aimState .nonPerishable ybar γ b h yhat1 d (n + 1)).1 ∧
      (aimState .nonPerishable ybar γ b h yhat1 d (n + 1)).1 ≤ ybar ∧
      (aimState .nonPerishable ybar γ b h yhat1 d (n + 1)).2 -
        (aimState .nonPerishable ybar γ b h yhat1 d (n + 1)).1 ≤ auxQueue ρ d (n + 1) := by
    intro n
    induction n with
    | zero => simpa [aimState, auxQueue] using And.intro hyhat1.1 (And.intro hyhat1.2 (le_refl (0 : ℝ)))
    | succ n ih =>
      let a := (aimState .nonPerishable ybar γ b h yhat1 d (n + 1)).1
      let y := (aimState .nonPerishable ybar γ b h yhat1 d (n + 1)).2
      let e := stepSize γ ybar b h (n + 1)
      let D : ℝ := d n
      let a' := projInterval ybar (a - e * gradEst h b D a)
      have hp := hproj (a - e * gradEst h b D a)
      have hs := hstep (n + 1) (by omega)
      have hdrop : a - a' ≤ ρ / Real.sqrt (n + 1 : ℕ) := by
        have hl : a - e * h ≤ a' := by
          apply le_trans _ (le_max_left _ _)
          apply le_min
          · unfold gradEst
            split_ifs
            · rfl
            · nlinarith [hs.1]
          · dsimp [a] at *
            nlinarith [ih.2.1]
        linarith [hs.2]
      have hq : 0 ≤ auxQueue ρ d (n + 1) := by
        cases n with
        | zero => simp [auxQueue]
        | succ n => exact le_max_right _ _
      have hD : 0 ≤ D := (d n).coe_nonneg
      have hbound : max a' (max (y - D) 0) - a' ≤
          max (auxQueue ρ d (n + 1) + ρ / Real.sqrt ((n : ℝ) + 1) - D) 0 := by
        have hcast : Real.sqrt (n + 1 : ℕ) = Real.sqrt ((n : ℝ) + 1) := by norm_cast
        rw [hcast] at hdrop
        have hiy : y - a ≤ auxQueue ρ d (n + 1) := ih.2.2
        have hn := le_max_right (auxQueue ρ d (n + 1) + ρ / Real.sqrt ((n : ℝ) + 1) - D) 0
        have hhq := le_max_left (auxQueue ρ d (n + 1) + ρ / Real.sqrt ((n : ℝ) + 1) - D) 0
        apply sub_le_iff_le_add.mpr
        apply max_le
        · linarith
        · apply max_le <;> linarith [hp.1]
      simpa [aimState, nextOnHand, auxQueue, a', a, y, e, D] using
        And.intro hp.1 (And.intro hp.2 hbound)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  exact (hall n).2.2

#print axioms solution
