-- Prove2me | solution 1 for AlgMechDesign.CompBonus.cb_truthful
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:05:25.541258+00:00
-- url     : https://prove2.me/submissions/4b4b9e8c-820e-4190-9466-edf0a62bb877

import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

set_option autoImplicit false
open AlgMechDesign.CompBonus

private theorem gT_corrStar_eq {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ)
    (x : Fin k → Fin n) : gT x (corrStar x t) = makespan t x := by
  unfold gT makespan load corrStar
  congr 1
  funext l
  apply Finset.sum_congr rfl
  intro j hj
  have h := (Finset.mem_filter.mp hj).2
  rw [h]

theorem solution {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc)
    (i : Fin n) (ti : Fin k → ℝ) (hti : IsAgentType ti) :
    Dominant alloc (cbPay alloc) i ti ti (fun _ j => ti j) := by
  refine ⟨hti, ?_, ?_⟩
  · intro x j hj
    exact le_rfl
  · intro d hd E di' hdi' ei' hei'
    let t := Function.update d i ti
    let u := Function.update d i di'
    have ht : IsType t := by
      intro l j
      by_cases hl : l = i
      · subst l
        simpa [t] using hti j
      · simpa [t, hl] using hd l j
    have htrue :
        corr i (alloc t) t (actualTimes alloc t (Function.update E i (fun _ j => ti j))) =
          corrStar (alloc t) t := by
      funext j
      by_cases hj : alloc t j = i
      · simp [corr, corrStar, actualTimes, hj, t]
      · simp [corr, corrStar, hj]
    have hmono : gT (alloc u) (corrStar (alloc u) t) ≤
        gT (alloc u) (corr i (alloc u) u (actualTimes alloc u (Function.update E i ei'))) := by
      unfold gT
      apply Finset.sup'_mono_fun
      intro l hl
      apply Finset.sum_le_sum
      intro j hj
      by_cases he : alloc u j = i
      · have h := hei' (alloc u) j he
        simpa [corrStar, corr, actualTimes, he, t] using h
      · simp [corrStar, corr, he, t, u]
    simp only [utility, cbPay, compensation, bonus, add_sub_cancel_left]
    change -gT (alloc u) (corr i (alloc u) u (actualTimes alloc u (Function.update E i ei'))) ≤
      -gT (alloc t) (corr i (alloc t) t
        (actualTimes alloc t (Function.update E i (fun _ j => ti j))))
    rw [htrue]
    apply neg_le_neg
    calc
      gT (alloc t) (corrStar (alloc t) t) ≤ gT (alloc u) (corrStar (alloc u) t) := by
        simpa only [gT_corrStar_eq] using hopt t ht (alloc u)
      _ ≤ _ := hmono
