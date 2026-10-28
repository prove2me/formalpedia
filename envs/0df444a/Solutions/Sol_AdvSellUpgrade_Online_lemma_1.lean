-- Prove2me | solution 1 for AdvSellUpgrade.Online.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:50:58.399558+00:00
-- url     : https://prove2.me/submissions/63481c21-3975-41cb-aa6c-4caab72b1440

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace Aux_ASU1
open AdvSellUpgrade.Online

lemma psi_eq (mu cbar lam c : ℝ) (hlam : 0 < lam) (hml : lam < mu) (hcb : 0 < cbar)
    (hc : 0 ≤ c) :
    c * (WR mu cbar lam c - WF mu cbar lam c) =
      c * lam ^ 2 * cbar / (mu * (mu - lam) * (cbar * (mu - lam) + lam * c)) := by
  have hmu : 0 < mu := by linarith
  have h1 : mu - lam ≠ 0 := by intro h; linarith
  have h2 : 0 < cbar * (mu - lam) + lam * c := by
    have : 0 < cbar * (mu - lam) := mul_pos hcb (by linarith)
    nlinarith
  have h3 : mu - (1 - c / cbar) * lam ≠ 0 := by
    have : mu - (1 - c / cbar) * lam = (cbar * (mu - lam) + lam * c) / cbar := by
      field_simp; ring
    rw [this]; exact (div_pos h2 hcb).ne'
  unfold WR WF
  field_simp
  ring

lemma single (mu cbar lam d c : ℝ) (hlam : 0 < lam) (hml : lam < mu) (hcb : 0 < cbar)
    (hd : 0 ≤ d) : IsSpotEqCutoff mu cbar lam d c ↔ c = cS mu cbar lam d := by
  have hmu : 0 < mu := by linarith
  have hml' : 0 < mu - lam := by linarith
  have hthr : lam ^ 2 * cbar / (mu ^ 2 * (mu - lam)) =
      cbar * (WR mu cbar lam cbar - WF mu cbar lam cbar) := by
    rw [psi_eq mu cbar lam cbar hlam hml hcb hcb.le]
    field_simp
    ring
  unfold IsSpotEqCutoff cS
  constructor
  · rintro (⟨hc0, hcc, hdeq⟩ | ⟨hceq, hle⟩)
    · rw [psi_eq mu cbar lam c hlam hml hcb hc0] at hdeq
      have hden : 0 < cbar * (mu - lam) + lam * c := by
        have : 0 < cbar * (mu - lam) := mul_pos hcb hml'
        nlinarith
      have hlt : d < lam ^ 2 * cbar / (mu ^ 2 * (mu - lam)) := by
        rw [hdeq, div_lt_div_iff₀ (by positivity) (by positivity)]
        have : c * mu < cbar * (mu - lam) + lam * c := by nlinarith
        have hk : 0 < lam ^ 2 * cbar * (mu * (mu - lam)) := by positivity
        nlinarith
      rw [if_pos hlt]
      have hD : 0 < lam ^ 2 * cbar - d * mu * (mu - lam) * lam := by
        rw [lt_div_iff₀ (by positivity)] at hlt
        have : d * mu * (mu - lam) * lam ≤ d * mu * (mu - lam) * mu :=
          mul_le_mul_of_nonneg_left hml.le (by positivity)
        nlinarith
      rw [eq_div_iff hD.ne', hdeq]
      field_simp
      ring
    · rw [hceq, if_neg (by rw [hthr]; exact not_lt.mpr hle)]
  · intro hc
    by_cases hlt : d < lam ^ 2 * cbar / (mu ^ 2 * (mu - lam))
    · rw [if_pos hlt] at hc
      left
      have hD : 0 < lam ^ 2 * cbar - d * mu * (mu - lam) * lam := by
        rw [lt_div_iff₀ (by positivity)] at hlt
        have : d * mu * (mu - lam) * lam ≤ d * mu * (mu - lam) * mu :=
          mul_le_mul_of_nonneg_left hml.le (by positivity)
        nlinarith
      have hc0 : 0 ≤ c := by rw [hc]; positivity
      refine ⟨hc0, ?_, ?_⟩
      · rw [hc, div_lt_iff₀ hD]
        rw [lt_div_iff₀ (by positivity)] at hlt
        nlinarith
      · rw [psi_eq mu cbar lam c hlam hml hcb hc0]
        have hcD : c * (lam ^ 2 * cbar - d * mu * (mu - lam) * lam) =
            d * mu * (mu - lam) ^ 2 * cbar := by
          rw [hc, div_mul_cancel₀ _ hD.ne']
        have hden : 0 < cbar * (mu - lam) + lam * c := by
          have : 0 < cbar * (mu - lam) := mul_pos hcb hml'
          nlinarith
        symm
        rw [div_eq_iff (by positivity)]
        linear_combination hcD
    · rw [if_neg hlt] at hc
      right
      refine ⟨hc, ?_⟩
      rw [← hthr]
      exact not_lt.mp hlt

end Aux_ASU1

open AdvSellUpgrade.Online in
theorem solution (P : Params) (hP : P.Standing) (Ps ch cl : ℝ) (hPs : P.Bs ≤ Ps) :
    (IsSpotEqCutoff P.mu P.cbar P.lamH (Ps - P.Bs) ch ∧
        IsSpotEqCutoff P.mu P.cbar P.lamL (Ps - P.Bs) cl) ↔
      (ch, cl) =
        (if Ps - P.Bs < P.lamL ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamL)) then
          ((Ps - P.Bs) * P.mu * (P.mu - P.lamH) ^ 2 * P.cbar /
              (P.lamH ^ 2 * P.cbar - (Ps - P.Bs) * P.mu * (P.mu - P.lamH) * P.lamH),
            (Ps - P.Bs) * P.mu * (P.mu - P.lamL) ^ 2 * P.cbar /
              (P.lamL ^ 2 * P.cbar - (Ps - P.Bs) * P.mu * (P.mu - P.lamL) * P.lamL))
        else if Ps - P.Bs < P.lamH ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamH)) then
          ((Ps - P.Bs) * P.mu * (P.mu - P.lamH) ^ 2 * P.cbar /
              (P.lamH ^ 2 * P.cbar - (Ps - P.Bs) * P.mu * (P.mu - P.lamH) * P.lamH),
            P.cbar)
        else (P.cbar, P.cbar)) := by
  obtain ⟨hL, hLH, hHm, hcb, -, -⟩ := hP
  have hd : 0 ≤ Ps - P.Bs := by linarith
  rw [Aux_ASU1.single _ _ _ _ _ (by linarith) hHm hcb hd,
    Aux_ASU1.single _ _ _ _ _ hL (by linarith) hcb hd]
  have hthr : P.lamL ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamL)) <
      P.lamH ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamH)) := by
    have hmL : 0 < P.mu - P.lamL := by linarith
    have hmH : 0 < P.mu - P.lamH := by linarith
    have hmu : 0 < P.mu := by linarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have key : P.lamL ^ 2 * (P.mu - P.lamH) < P.lamH ^ 2 * (P.mu - P.lamL) := by
      have p1 : 0 < P.lamH - P.lamL := by linarith
      have p2 : 0 < P.mu * (P.lamH + P.lamL) - P.lamL * P.lamH := by
        have : P.lamL * P.lamH < P.lamL * P.mu := mul_lt_mul_of_pos_left hHm hL
        nlinarith [mul_pos hmu (by linarith : (0:ℝ) < P.lamH)]
      nlinarith [mul_pos p1 p2]
    have hk : 0 < P.cbar * P.mu ^ 2 := by positivity
    nlinarith
  unfold cS
  by_cases h1 : Ps - P.Bs < P.lamL ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamL))
  · rw [if_pos h1, if_pos (lt_trans h1 hthr), if_pos h1, Prod.ext_iff]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : Ps - P.Bs < P.lamH ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamH))
    · rw [if_pos h2, if_pos h2, Prod.ext_iff]
    · rw [if_neg h2, if_neg h2, Prod.ext_iff]
