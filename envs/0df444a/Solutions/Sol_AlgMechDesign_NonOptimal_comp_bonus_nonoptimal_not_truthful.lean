-- Prove2me | solution 1 for AlgMechDesign.NonOptimal.comp_bonus_nonoptimal_not_truthful
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:56:02.257963+00:00
-- url     : https://prove2.me/submissions/fed90a6c-7f9b-42ea-9ec4-5b75033ebe1e

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

private theorem profile_mono {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (htruth : Truthful alloc) (t : Fin n → Fin k → ℝ) (ht : IsType t) (o : Fin k → Fin n)
    (M : ℝ) (hM : ∀ i j, t i j ≤ M) :
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

private theorem transformed_bounds {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ)
    (ht : IsType t) (o : Fin k → Fin n) (M : ℝ) (hM : ∀ i j, t i j ≤ M) :
    makespan (sType t o M) o = makespan t o ∧
      ∀ y : Fin k → Fin n, y ≠ o → M ≤ makespan (sType t o M) y := by
  have hpoint : ∀ i j, t i j ≤ sType t o M i j := by
    intro i j
    unfold sType offOpt
    split_ifs
    · exact le_rfl
    · exact hM i j
  constructor
  · unfold makespan
    congr 1
    funext i
    unfold load
    apply Finset.sum_congr rfl
    intro j hj
    simp [sType, offOpt, (Finset.mem_filter.mp hj).2]
  · intro y hyo
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hyo
    have hterm : sType t o M (y j) j = M := by simp [sType, offOpt, Ne.symm hj]
    have hload : M ≤ load (sType t o M) y (y j) := by
      calc
        M = sType t o M (y j) j := hterm.symm
        _ ≤ load (sType t o M) y (y j) := by
          unfold load
          apply Finset.single_le_sum
          · intro q hq
            exact (le_of_lt (ht (y j) q)).trans (hpoint (y j) q)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact hload.trans (Finset.le_sup' (load (sType t o M) y) (Finset.mem_univ _))

theorem solution {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (happrox : ∃ c : ℝ, ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin n,
      makespan t (alloc t) ≤ c * makespan t y)
    (hnonopt : ∃ t : Fin n → Fin k → ℝ, IsType t ∧ ∃ y : Fin k → Fin n,
      makespan t y < makespan t (alloc t)) :
    ¬ Truthful alloc := by
  intro htruth
  obtain ⟨c, hc⟩ := happrox
  obtain ⟨t, ht, o, hgap⟩ := hnonopt
  let A : ℝ := ∑ i, ∑ j, t i j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi =>
    Finset.sum_nonneg (fun j hj => le_of_lt (ht i j)))
  have hentry : ∀ i j, t i j ≤ A := by
    intro i j
    calc
      t i j ≤ ∑ q, t i q := Finset.single_le_sum (fun q hq => le_of_lt (ht i q)) (Finset.mem_univ _)
      _ ≤ A := Finset.single_le_sum (fun l hl => Finset.sum_nonneg (fun q hq => le_of_lt (ht l q))) (Finset.mem_univ _)
  let M := A + |c * makespan t o| + 1
  have hM : ∀ i j, t i j ≤ M := by
    intro i j
    dsimp [M]
    linarith [hentry i j, abs_nonneg (c * makespan t o)]
  have hlarge : c * makespan t o < M := by
    dsimp [M]
    linarith [le_abs_self (c * makespan t o)]
  have hs : IsType (sType t o M) := by
    intro i j
    unfold sType offOpt
    split_ifs
    · exact ht i j
    · exact (ht i j).trans_le (hM i j)
  have hmono := profile_mono alloc htruth t ht o M hM
  have hb := transformed_bounds t ht o M hM
  have hne : alloc (sType t o M) ≠ o := by
    intro he
    rw [he, hb.1] at hmono
    linarith
  have hlo := hb.2 (alloc (sType t o M)) hne
  have hhi := hc (sType t o M) hs o
  rw [hb.1] at hhi
  linarith

