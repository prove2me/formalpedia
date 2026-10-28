-- Prove2me | solution 1 for AdvSellUpgrade.Online.prop3_cutoff_problem
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:55:45.834224+00:00
-- url     : https://prove2.me/submissions/33873398-448b-4436-a456-d83fd2ab5fa1

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace Aux_ASU3
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

end Aux_ASU3

open AdvSellUpgrade.Online in
theorem solution (mu cbar lam : ℝ) (hlam : 0 < lam) (hlammu : lam < mu)
    (hcbar : 0 < cbar) :
    StrictMonoOn (fun ch => ch * (WR mu cbar lam ch - WF mu cbar lam ch)) (Set.Icc 0 cbar) ∧
      cFn mu cbar lam ∈ Set.Ioo 0 cbar ∧
      (∀ ch ∈ Set.Ioo 0 cbar, revCut mu cbar lam ch ≤ revCut mu cbar lam (cFn mu cbar lam)) ∧
      revCut mu cbar lam (cFn mu cbar lam) = piFn mu cbar lam ∧
      cFn mu cbar lam * (WR mu cbar lam (cFn mu cbar lam) - WF mu cbar lam (cFn mu cbar lam))
        = pFn mu cbar lam := by
  have hmu : 0 < mu := by linarith
  have hml : 0 < mu - lam := by linarith
  set s := Real.sqrt (mu * (mu - lam)) with hsdef
  have hs2 : s ^ 2 = mu * (mu - lam) := Real.sq_sqrt (by positivity)
  have hs_lo : mu - lam < s := by
    rw [hsdef, Real.lt_sqrt hml.le]
    nlinarith
  have hs_hi : s < mu := by
    rw [hsdef, Real.sqrt_lt' hmu]
    nlinarith
  have hs0 : 0 < s := by linarith
  have hc : cFn mu cbar lam = (s - (mu - lam)) * cbar / lam := rfl
  have hcpos : 0 < cFn mu cbar lam := by rw [hc]; apply div_pos _ hlam; nlinarith
  have hclt : cFn mu cbar lam < cbar := by
    rw [hc, div_lt_iff₀ hlam]; nlinarith
  have hz : ∀ c, mu * cbar - (cbar - c) * lam = cbar * (mu - lam) + lam * c := fun c => by ring
  set cs := cFn mu cbar lam with hcs
  have e1 : lam * cs = cbar * (s - (mu - lam)) := by
    rw [hc]; field_simp
  have e2 : lam * (cbar - cs) = cbar * (mu - s) := by linarith
  have e3 : mu * cbar - (cbar - cs) * lam = cbar * s := by linarith
  have hsq : Real.sqrt mu * Real.sqrt (mu - lam) = s := by
    rw [hsdef, Real.sqrt_mul hmu.le]
  have e5 : (Real.sqrt mu - Real.sqrt (mu - lam)) ^ 2 = 2 * mu - lam - 2 * s := by
    have a1 : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt hmu.le
    have a2 : Real.sqrt (mu - lam) ^ 2 = mu - lam := Real.sq_sqrt hml.le
    nlinarith
  have hVstar : revCut mu cbar lam cs = cbar * (2 * mu - lam - 2 * s) / (mu * (mu - lam)) := by
    unfold revCut
    rw [e3]
    have e4 : lam ^ 2 * cs * (cbar - cs) = (lam * cs) * (lam * (cbar - cs)) := by ring
    rw [e4, e1, e2, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (cbar ^ 2 * mu * (mu - lam)) * hs2
  refine ⟨?_, ⟨hcpos, hclt⟩, ?_, ?_, ?_⟩
  · intro c1 hc1 c2 hc2 h12
    simp only
    rw [Aux_ASU3.psi_eq mu cbar lam c1 hlam hlammu hcbar hc1.1,
      Aux_ASU3.psi_eq mu cbar lam c2 hlam hlammu hcbar hc2.1]
    have hA : 0 < cbar * (mu - lam) := mul_pos hcbar hml
    have d1 : 0 < cbar * (mu - lam) + lam * c1 := by nlinarith [hc1.1]
    have d2 : 0 < cbar * (mu - lam) + lam * c2 := by nlinarith [hc2.1]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have key : c1 * (cbar * (mu - lam) + lam * c2) < c2 * (cbar * (mu - lam) + lam * c1) := by
      nlinarith
    have hk : 0 < lam ^ 2 * cbar * (mu * (mu - lam)) := by positivity
    nlinarith
  · intro ch hch
    rw [hVstar]
    unfold revCut
    rw [hz ch]
    have hzpos : 0 < cbar * (mu - lam) + lam * ch := by
      have : 0 < cbar * (mu - lam) := mul_pos hcbar hml
      nlinarith [hch.1]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : lam ^ 2 * ch * (cbar - ch) =
        cbar * (2 * mu - lam - 2 * s) * (cbar * (mu - lam) + lam * ch) -
          (cbar * (mu - lam) + lam * ch - cbar * s) ^ 2 := by
      linear_combination (cbar ^ 2) * hs2
    rw [key]
    have hk : 0 < mu * (mu - lam) := by positivity
    nlinarith [sq_nonneg (cbar * (mu - lam) + lam * ch - cbar * s)]
  · rw [hVstar]
    unfold piFn
    rw [e5]
    ring
  · rw [Aux_ASU3.psi_eq mu cbar lam cs hlam hlammu hcbar hcpos.le]
    have e6 : cbar * (mu - lam) + lam * cs = cbar * s := by linarith
    have e7 : cs * lam ^ 2 * cbar = (lam * cs) * lam * cbar := by ring
    rw [e6, e7, e1]
    unfold pFn
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (cbar ^ 2 * lam * mu * (mu - lam)) * hs2
