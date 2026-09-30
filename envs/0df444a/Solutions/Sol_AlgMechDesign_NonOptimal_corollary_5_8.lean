-- Prove2me | solution 1 for AlgMechDesign.NonOptimal.corollary_5_8
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:53:46.722491+00:00
-- url     : https://prove2.me/submissions/d672d803-2718-4661-8cf9-7f0bd121e357

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
    (ho : IsOptimalFor t o) (M : ℝ) (hM : ∀ i j, t i j ≤ M) :
    makespan t (alloc t) ≤ makespan (sType t o M) (alloc (sType t o M)) := by
  classical
  have hpoint : ∀ i j, t i j ≤ sType t o M i j := by
    intro i j
    unfold sType offOpt
    split_ifs
    · exact le_rfl
    · exact hM i j
  let v : Finset (Fin n) → Fin n → Fin k → ℝ :=
    fun S i j => if i ∈ S then sType t o M i j else t i j
  have hv : ∀ S, IsType (v S) := by
    intro S i j
    dsimp [v]
    split_ifs
    · exact (ht i j).trans_le (hpoint i j)
    · exact ht i j
  have hm : ∀ S, makespan t (alloc t) ≤ makespan (v S) (alloc (v S)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [v]
    | @insert i S hi ih =>
        have hu : v (insert i S) = Function.update (v S) i (sType t o M i) := by
          funext l j
          by_cases he : l = i
          · subst l
            simp [v]
          · simp [v, he]
        rw [hu]
        apply ih.trans
        apply coordinate_mono alloc htruth (v S) (hv S) i (sType t o M i)
        · intro j
          exact (ht i j).trans_le (hpoint i j)
        · intro j
          simpa [v, hi] using hpoint i j
  simpa [v] using hm univ

