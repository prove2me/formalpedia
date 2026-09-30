-- Prove2me | solution 1 for AlgMechDesign.NonOptimal.claim_5_7
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:52:54.524608+00:00
-- url     : https://prove2.me/submissions/6ae43f1e-81c8-460e-9393-887e4f507df0

import Definitions.Def_AlgMechDesign_NonOptimal_Model

set_option autoImplicit false
open AlgMechDesign.NonOptimal Finset

private theorem gT_corrStar_eq {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ)
    (x : Fin k → Fin n) : gT x (corrStar x t) = makespan t x := by
  unfold gT makespan load corrStar
  congr 1
  funext l
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

private theorem coordinate_mono {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (htruth : Truthful alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) (r : Fin k → ℝ)
    (hr : IsAgentType r) (hle : ∀ j, t i j ≤ r j) :
    makespan t (alloc t) ≤ makespan (Function.update t i r) (alloc (Function.update t i r)) := by
  obtain ⟨ei, heifeas, hdom⟩ := htruth i (t i) (ht i)
  let u := Function.update t i r
  let E : Fin n → ExecPlan n k := fun _ _ _ => 0
  have hdev : corr i (alloc u) u (actualTimes alloc u (Function.update E i (fun _ => t i))) =
      corrStar (alloc u) t := by
    funext j
    by_cases he : alloc u j = i
    · simp [corr, corrStar, actualTimes, he]
    · simp [corr, corrStar, he, u]
  have htrue : gT (alloc t) (corrStar (alloc t) t) ≤
      gT (alloc t) (corr i (alloc t) t (actualTimes alloc t (Function.update E i ei))) := by
    unfold gT
    apply Finset.sup'_mono_fun
    intro l hl
    apply Finset.sum_le_sum
    intro j hj
    by_cases he : alloc t j = i
    · simpa [corrStar, corr, actualTimes, he] using heifeas (alloc t) j he
    · simp [corrStar, corr, he]
  have hcomp := hdom.2.2 t ht E r hr (fun _ => t i) (by intro x j hj; exact le_rfl)
  simp only [Function.update_eq_self, utility, cbPay, compensation, bonus, add_sub_cancel_left] at hcomp
  change -gT (alloc u) (corr i (alloc u) u
    (actualTimes alloc u (Function.update E i (fun _ => t i)))) ≤
      -gT (alloc t) (corr i (alloc t) t (actualTimes alloc t (Function.update E i ei))) at hcomp
  rw [hdev] at hcomp
  have hmid := htrue.trans (neg_le_neg_iff.mp hcomp)
  rw [gT_corrStar_eq, gT_corrStar_eq] at hmid
  apply hmid.trans
  unfold makespan
  apply Finset.sup'_mono_fun
  intro l hl
  apply Finset.sum_le_sum
  intro j hj
  by_cases he : l = i
  · subst l
    simpa [u] using hle j
  · simp [u, he]

theorem solution {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (htruth : Truthful alloc) (t : Fin n → Fin k → ℝ) (ht : IsType t) (o : Fin k → Fin n)
    (ho : IsOptimalFor t o) (M : ℝ) (hM : ∀ i j, t i j ≤ M) (i : Fin n) :
    makespan t (alloc t) ≤
      makespan (Function.update t i (offOpt t o M i))
        (alloc (Function.update t i (offOpt t o M i))) := by
  have hle : ∀ j, t i j ≤ offOpt t o M i j := by
    intro j
    unfold offOpt
    split_ifs
    · exact le_rfl
    · exact hM i j
  exact coordinate_mono alloc htruth t ht i (offOpt t o M i)
    (fun j => (ht i j).trans_le (hle j)) hle
