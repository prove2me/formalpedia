-- Prove2me | solution 1 for AggGameNet.Sync.relation_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:23:01.029367+00:00
-- url     : https://prove2.me/submissions/d40e4d6d-ff65-420d-9797-81516a16ee12

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_AggGameNet_Sync_lemma_2

namespace AggGameNet.Sync

/-- variational characterisation of a nearest point on a convex set -/
private lemma isProj_inner_le {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {z p : E n}
    (hp : ChanPangGQVI.Shared.IsProj S z p) : ∀ q ∈ S, inner ℝ (z - p) (q - p) ≤ 0 := by
  have hne : Nonempty S := ⟨⟨p, hp.1⟩⟩
  have heq : ‖z - p‖ = ⨅ w : S, ‖z - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      rw [norm_sub_rev z p, norm_sub_rev z w]
      exact hp.2 w w.2
    · have hb : BddBelow (Set.range (fun w : S => ‖z - (w : E n)‖)) :=
        ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
      exact ciInf_le (f := fun w : S => ‖z - (w : E n)‖) hb ⟨p, hp.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hS hp.1).1 heq

private lemma isProj_dist_le {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {z p : E n}
    (hp : ChanPangGQVI.Shared.IsProj S z p) : ∀ q ∈ S, ‖p - q‖ ^ 2 ≤ ‖z - q‖ ^ 2 := by
  intro q hq
  have h := isProj_inner_le hS hp q hq
  have e : z - q = (z - p) - (q - p) := by abel
  have e2 : p - q = -(q - p) := by abel
  rw [e, norm_sub_sq_real (z - p) (q - p), e2, norm_neg]
  nlinarith [sq_nonneg ‖z - p‖]

end AggGameNet.Sync

open AggGameNet.Sync

theorem solution {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F)
    (Lbar : Fin N → ℝ) (h3 : Assumption3 K F Lbar)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (α : ℕ → ℝ)
    (x v : ℕ → Fin N → E n) (hrun : IsSyncRun K F W α x v)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hα : ∀ k, 0 ≤ α k)
    (xs : Fin N → E n) (hxs : IsVISol K F xs)
    (C Fmax M : ℝ)
    (hC : ∀ i k, ‖F i (x k i) ((N : ℝ) • vhat W v k i)‖ ≤ C)
    (hF : ∀ i, ∀ xi ∈ K i, ∀ u ∈ Kbar K, ‖F i xi u‖ ≤ Fmax)
    (hM : ∀ i, ∀ a ∈ K i, ‖a‖ ≤ M) :
    ∀ k,
      (∑ i, ‖x (k + 1) i - xs i‖ ^ 2) ≤
        (∑ i, ‖x k i - xs i‖ ^ 2) +
        (N : ℝ) * (2 * C ^ 2 + 2 * Fmax ^ 2) * α k ^ 2 +
        4 * α k * M * (N : ℝ) *
          (∑ i, Lbar i * ‖vhat W v k i - yavg v k‖) -
        2 * α k *
          (∑ i, inner ℝ (phi F (x k) i - phi F xs i) (x k i - xs i)) := by
  intro k
  have hfeas : ∀ k i, x k i ∈ K i := by
    intro k i
    cases k with
    | zero => exact hrun.1 i
    | succ k => exact ((hrun.2.2 k i).1).1
  have hmean := lemma_2 hN W x v hcol hrun.2.1 (fun k i => (hrun.2.2 k i).2) k
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNy : (N : ℝ) • yavg v k = ∑ j, x k j := by
    rw [hmean, smul_smul, mul_one_div_cancel hNne, one_smul]
  have hαk := hα k
  -- per-agent estimate
  have hi : ∀ i, ‖x (k + 1) i - xs i‖ ^ 2 ≤ ‖x k i - xs i‖ ^ 2 + α k ^ 2 * C ^ 2 +
      4 * α k * M * (N : ℝ) * (Lbar i * ‖vhat W v k i - yavg v k‖) -
      2 * α k * inner ℝ (x k i - xs i) (phi F (x k) i) := by
    intro i
    set g := F i (x k i) ((N : ℝ) • vhat W v k i) with hg
    set φi := phi F (x k) i with hφi
    set d := x k i - xs i with hd
    have hp := (hrun.2.2 k i).1
    have h0 := isProj_dist_le ((h1.1 i).2.2) hp (xs i) (hxs.1 i)
    have e : x k i - α k • g - xs i = d - α k • g := by simp only [hd]; abel
    rw [e, norm_sub_sq_real d (α k • g), real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs] at h0
    have hgC : ‖g‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC i k) 2
    have hφ : φi = F i (x k i) ((N : ℝ) • yavg v k) := by
      simp only [hφi, phi, hNy]
    have hLip : ‖g - φi‖ ≤ Lbar i * ((N : ℝ) * ‖vhat W v k i - yavg v k‖) := by
      rw [hφ, hg]
      have := (h3.2 i (x k i) (hfeas k i) ((N : ℝ) • vhat W v k i) ((N : ℝ) • yavg v k))
      rwa [← smul_sub, norm_smul, Real.norm_natCast] at this
    have hdM : ‖d‖ ≤ 2 * M := by
      have := norm_sub_le (x k i) (xs i)
      have := hM i _ (hfeas k i)
      have := hM i _ (hxs.1 i)
      simp only [hd]; linarith
    have hsplit : inner ℝ d g = inner ℝ d φi + inner ℝ d (g - φi) := by
      rw [inner_sub_right]; ring
    have hcs : -(‖d‖ * ‖g - φi‖) ≤ inner ℝ d (g - φi) :=
      neg_le_of_abs_le (abs_real_inner_le_norm d (g - φi))
    have hprod : ‖d‖ * ‖g - φi‖ ≤ 2 * M * (Lbar i * ((N : ℝ) * ‖vhat W v k i - yavg v k‖)) :=
      mul_le_mul hdM hLip (norm_nonneg _) (by linarith [norm_nonneg d])
    have h4 := mul_le_mul_of_nonneg_left hprod hαk
    have h5 := mul_le_mul_of_nonneg_left hgC (sq_nonneg (α k))
    have h6 := mul_le_mul_of_nonneg_left hcs hαk
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hvi := hxs.2 (x k) (hfeas k)
  have hsplit : ∑ i, inner ℝ (phi F (x k) i - phi F xs i) (x k i - xs i) =
      ∑ i, inner ℝ (x k i - xs i) (phi F (x k) i) - ∑ i, inner ℝ (x k i - xs i) (phi F xs i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sub_left, real_inner_comm, real_inner_comm (x k i - xs i)]
  have hextra : 0 ≤ (N : ℝ) * α k ^ 2 * (C ^ 2 + 2 * Fmax ^ 2) := by positivity
  have h7 := mul_le_mul_of_nonneg_left hvi (by linarith : (0:ℝ) ≤ 2 * α k)
  unfold phi at hsplit hvi h7 hsum ⊢
  rw [hsplit]
  nlinarith
