-- Prove2me | solution 1 for AdvSellUpgrade.Online.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:56:53.192198+00:00
-- url     : https://prove2.me/submissions/40da7dde-5363-4e9a-abaa-33d321fb9cc9

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting
import Theorems.Thm_AdvSellUpgrade_Online_proposition_6
import Theorems.Thm_AdvSellUpgrade_Online_proposition_5_gap

namespace Aux_ASUT1R
open AdvSellUpgrade.Online

/-- `p` is strictly increasing in the rate. -/
lemma p_mono (mu cbar l1 l2 : ℝ) (h1 : 0 < l1) (h12 : l1 < l2) (h2 : l2 < mu) (hcb : 0 < cbar) :
    pFn mu cbar l1 < pFn mu cbar l2 := by
  have hmu : 0 < mu := by linarith
  unfold pFn
  have hs1 : Real.sqrt (mu * (mu - l2)) < Real.sqrt (mu * (mu - l1)) :=
    Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
  have hs1' : Real.sqrt (mu * (mu - l1)) < mu := by
    rw [Real.sqrt_lt' hmu]; nlinarith
  have a1 : 0 < (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar := by
    have : 0 < mu - Real.sqrt (mu * (mu - l1)) := by linarith
    positivity
  have a12 : (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar <
      (mu - Real.sqrt (mu * (mu - l2))) * l2 * cbar := by
    have e : 0 < mu - Real.sqrt (mu * (mu - l1)) := by linarith
    have : (mu - Real.sqrt (mu * (mu - l1))) * l1 < (mu - Real.sqrt (mu * (mu - l2))) * l2 := by
      nlinarith
    exact mul_lt_mul_of_pos_right this hcb
  have b2 : 0 < (mu - l2) * mu ^ 2 := by
    have : 0 < mu - l2 := by linarith
    positivity
  have b12 : (mu - l2) * mu ^ 2 < (mu - l1) * mu ^ 2 := by
    have : 0 < mu ^ 2 := by positivity
    nlinarith
  calc (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar / ((mu - l1) * mu ^ 2)
      < (mu - Real.sqrt (mu * (mu - l1))) * l1 * cbar / ((mu - l2) * mu ^ 2) :=
        div_lt_div_of_pos_left a1 b2 b12
    _ < _ := div_lt_div_of_pos_right a12 b2

/-- An AUS point whose upgrade option is not cheaper than the spot fast-track ticket is an AS point
with the same objective value. -/
lemma aus_to_as (P : Params) (cr cf Pa Ps K : ℝ) (hf : FeasAUS P cr cf Pa Ps K)
    (hK : P.alpha * Ps + (1 - P.alpha) * P.Bs ≤ P.Ba + P.alpha * K) :
    FeasAS P cr cf Pa Ps ∧ objAS P cr cf Pa Ps = objAUS P cr cf Pa Ps K := by
  have hmin := min_eq_left hK
  obtain ⟨f1, -, f2, f3, f4, f5, f6, f7⟩ := hf
  rw [hmin] at f2 f4
  refine ⟨⟨f1, f2, f3, f4, f5, f6, f7⟩, ?_⟩
  unfold objAS objAUS
  rw [hmin]

/-- Every AS point is an AUS point (with a large upgrading fee) with the same objective value. -/
lemma as_sub_aus (P : Params) (hP : P.Standing) : asValues P ⊆ ausValues P := by
  rintro v ⟨cr, cf, Pa, Ps, hf, rfl⟩
  obtain ⟨-, -, -, -, ha0, -⟩ := hP
  refine ⟨cr, cf, Pa, Ps, max (Pa - P.Ba) ((P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba) / P.alpha),
    ?_, ?_⟩
  · have hK : P.alpha * Ps + (1 - P.alpha) * P.Bs ≤ P.Ba + P.alpha *
        max (Pa - P.Ba) ((P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba) / P.alpha) := by
      have := mul_le_mul_of_nonneg_left (le_max_right (Pa - P.Ba)
        ((P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba) / P.alpha)) ha0.le
      rw [mul_div_cancel₀ _ ha0.ne'] at this
      linarith
    have hmin := min_eq_left hK
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
    refine ⟨f1, ?_, ?_, f3, ?_, f5, f6, f7⟩
    · have := le_max_left (Pa - P.Ba) ((P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba) / P.alpha)
      linarith
    · rw [hmin]; exact f2
    · rw [hmin]; exact f4
  · have hK : P.alpha * Ps + (1 - P.alpha) * P.Bs ≤ P.Ba + P.alpha *
        max (Pa - P.Ba) ((P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba) / P.alpha) := by
      have := mul_le_mul_of_nonneg_left (le_max_right (Pa - P.Ba)
        ((P.alpha * Ps + (1 - P.alpha) * P.Bs - P.Ba) / P.alpha)) ha0.le
      rw [mul_div_cancel₀ _ ha0.ne'] at this
      linarith
    unfold objAS objAUS
    rw [min_eq_left hK]

end Aux_ASUT1R

open AdvSellUpgrade.Online Aux_ASUT1R in
theorem solution (P : Params) (hP : P.Standing) :
    ∃ vAS vAUS : ℝ, IsLUB (asValues P) vAS ∧ IsGreatest (ausValues P) vAUS ∧
      (P.Bs - P.Ba ≤ P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) → vAS = vAUS) ∧
      (P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) < P.Bs - P.Ba →
        vAS < vAUS) := by
  obtain ⟨hG, -, p3, p4, p5⟩ := proposition_6 P hP
  have hP' := hP
  obtain ⟨hl0, hlh, hhm, hcb, ha0, ha1⟩ := hP'
  have hmono := p_mono P.mu P.cbar P.lamL P.lamH hl0 hlh hhm hcb
  have hsub := as_sub_aus P hP
  -- a trivially feasible AS point: no fast-track buyers
  have hne : (asValues P).Nonempty := by
    refine ⟨_, P.cbar, P.cbar,
      P.Bs + P.cbar * (WR P.mu P.cbar P.lamL P.cbar - WF P.mu P.cbar P.lamL P.cbar),
      P.Bs + P.cbar * (WR P.mu P.cbar P.lamL P.cbar - WF P.mu P.cbar P.lamL P.cbar),
      ⟨le_rfl, fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _), fun _ => ?_,
        hcb, le_rfl, le_rfl⟩, rfl⟩
    apply le_of_eq; ring
  have hbdd : BddAbove (asValues P) := ⟨_, fun x hx => hG.2 (hsub hx)⟩
  refine ⟨sSup (asValues P), _, isLUB_csSup hne hbdd, hG, fun hle => ?_, fun hlt => ?_⟩
  · -- the AUS optimum is attained by an AS point
    have hmem : P.alpha * piFn P.mu P.cbar P.lamH + (1 - P.alpha) * piFn P.mu P.cbar P.lamL
        + min P.Ba P.Bs ∈ asValues P := by
      rcases lt_or_ge (P.Bs - P.Ba) 0 with h | h
      · have hK := p3 h _ le_rfl
        refine ⟨_, _, _, _, (aus_to_as P _ _ _ _ _ hK.1 ?_).1,
          ((aus_to_as P _ _ _ _ _ hK.1 ?_).2.trans hK.2).symm⟩ <;>
        · have := mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_right 0
            (max ((P.Bs - P.Ba) / P.alpha + pFn P.mu P.cbar P.lamH)
              (P.Bs - P.Ba + P.alpha * pFn P.mu P.cbar P.lamH
                + (1 - P.alpha) * pFn P.mu P.cbar P.lamL)))) ha0.le
          rw [mul_add, mul_div_cancel₀ _ ha0.ne'] at this
          linarith
      · rcases lt_or_eq_of_le hle with h' | h'
        · have hK := (p4 h h').1 _ le_rfl
          have e : P.alpha * (pFn P.mu P.cbar P.lamH
              + (P.Ba - (1 - P.alpha) * P.Bs) / P.alpha) + (1 - P.alpha) * P.Bs
              = P.Ba + P.alpha * pFn P.mu P.cbar P.lamH := by field_simp; ring
          exact ⟨_, _, _, _, (aus_to_as P _ _ _ _ _ hK.1 e.le).1,
            ((aus_to_as P _ _ _ _ _ hK.1 e.le).2.trans hK.2).symm⟩
        · have hK := p5 h'.ge _ le_rfl
          have e : P.alpha * (P.alpha * pFn P.mu P.cbar P.lamH
              + (1 - P.alpha) * pFn P.mu P.cbar P.lamL + P.Ba) + (1 - P.alpha) * P.Bs
              ≤ P.Ba + P.alpha * pFn P.mu P.cbar P.lamH := by
            have : P.Bs = P.Ba + P.alpha * (pFn P.mu P.cbar P.lamH - pFn P.mu P.cbar P.lamL) := by
              linarith
            rw [this]; apply le_of_eq; ring
          exact ⟨_, _, _, _, (aus_to_as P _ _ _ _ _ hK.1 e).1,
            ((aus_to_as P _ _ _ _ _ hK.1 e).2.trans hK.2).symm⟩
    exact (IsGreatest.csSup_eq ⟨hmem, fun x hx => hG.2 (hsub hx)⟩)
  · obtain ⟨v, hv, hall⟩ := proposition_5_gap P hP hlt
    have hBa : P.Ba ≤ P.Bs := by nlinarith
    rw [min_eq_left hBa]
    refine lt_of_le_of_lt (csSup_le hne ?_) hv
    rintro x ⟨cr, cf, Pa, Ps, hf, rfl⟩
    exact hall cr cf Pa Ps hf
