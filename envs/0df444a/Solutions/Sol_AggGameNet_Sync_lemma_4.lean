-- Prove2me | solution 1 for AggGameNet.Sync.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:29:05.478784+00:00
-- url     : https://prove2.me/submissions/b66108dc-bd77-4edf-847a-d59a21381c71

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_AggGameNet_Sync_lemma_1
import Theorems.Thm_AggGameNet_Sync_lemma_2

namespace AggGameNet.Sync.L4aux

open ChanPangGQVI.Shared

lemma isProj_inner_le {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {z p : E n}
    (hp : IsProj S z p) : ∀ q ∈ S, inner ℝ (z - p) (q - p) ≤ 0 := by
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

lemma isProj_dist_le {n : ℕ} {S : Set (E n)} (hS : Convex ℝ S) {z p : E n}
    (hp : IsProj S z p) : ∀ q ∈ S, ‖p - q‖ ≤ ‖z - q‖ := by
  intro q hq
  have h := isProj_inner_le hS hp q hq
  have e : z - q = (z - p) - (q - p) := by abel
  have e2 : p - q = -(q - p) := by abel
  have : ‖p - q‖ ^ 2 ≤ ‖z - q‖ ^ 2 := by
    rw [e, norm_sub_sq_real (z - p) (q - p), e2, norm_neg]
    nlinarith [sq_nonneg ‖z - p‖]
  exact le_of_sq_le_sq (by simpa [abs_of_nonneg (norm_nonneg _)] using this) (norm_nonneg _)

/-- representation (14) of the aligned estimate -/
lemma vhat_repr {N n : ℕ} (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (x v : ℕ → Fin N → E n)
    (hinit : v 0 = x 0)
    (hrec : ∀ k i, v (k + 1) i = vhat W v k i + x (k + 1) i - x k i) :
    ∀ k i, vhat W v k i = ∑ l, Phi W 0 k i l • x 0 l +
      ∑ s ∈ Finset.Icc 1 k, ∑ j, Phi W s (k - s) i j • (x s j - x (s - 1) j) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [vhat, Phi, hinit]
  | succ k ih =>
    intro i
    have h1 : vhat W v (k + 1) i = ∑ j, W (k + 1) i j • vhat W v k j +
        ∑ j, W (k + 1) i j • (x (k + 1) j - x k j) := by
      rw [← Finset.sum_add_distrib]
      unfold vhat
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← smul_add, hrec]
      congr 1
      unfold vhat
      abel
    have A : ∑ j, W (k + 1) i j • vhat W v k j = ∑ l, Phi W 0 (k + 1) i l • x 0 l +
        ∑ s ∈ Finset.Icc 1 k, ∑ l, Phi W s (k + 1 - s) i l • (x s l - x (s - 1) l) := by
      simp only [ih, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      have hPhi0 : ∀ l, Phi W 0 (k + 1) i l = ∑ j, W (k + 1) i j * Phi W 0 k j l := by
        intro l
        simp only [Phi, Matrix.mul_apply, zero_add]
      have hPhis : ∀ s ∈ Finset.Icc 1 k, ∀ l,
          Phi W s (k + 1 - s) i l = ∑ j, W (k + 1) i j * Phi W s (k - s) j l := by
        intro s hs l
        have hsk : s ≤ k := (Finset.mem_Icc.1 hs).2
        have e : k + 1 - s = (k - s) + 1 := by omega
        rw [e]
        simp only [Phi, Matrix.mul_apply]
        have e2 : s + (k - s) + 1 = k + 1 := by omega
        rw [e2]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hPhi0, Finset.sum_smul]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hPhis s hs l, Finset.sum_smul]
    have B : ∑ s ∈ Finset.Icc 1 (k + 1), ∑ j, Phi W s (k + 1 - s) i j • (x s j - x (s - 1) j) =
        ∑ s ∈ Finset.Icc 1 k, ∑ l, Phi W s (k + 1 - s) i l • (x s l - x (s - 1) l) +
        ∑ j, W (k + 1) i j • (x (k + 1) j - x k j) := by
      rw [Finset.sum_Icc_succ_top (by omega)]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [Phi]
    rw [h1, A, B]
    abel

/-- representation (15) of the mean estimate -/
lemma yavg_repr {N n : ℕ} (hN : 0 < N) (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (x v : ℕ → Fin N → E n)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hinit : v 0 = x 0)
    (hrec : ∀ k i, v (k + 1) i = vhat W v k i + x (k + 1) i - x k i) :
    ∀ k, yavg v k = ∑ l, (1 / (N : ℝ)) • x 0 l +
      ∑ s ∈ Finset.Icc 1 k, ∑ j, (1 / (N : ℝ)) • (x s j - x (s - 1) j) := by
  have hm := lemma_2 hN W x v hcol hinit hrec
  intro k
  rw [hm k]
  induction k with
  | zero => simp [Finset.smul_sum]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih, Nat.add_sub_cancel,
      ← Finset.smul_sum, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => by abel)

lemma disagreement_repr {N n : ℕ} (hN : 0 < N) (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (x v : ℕ → Fin N → E n)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hinit : v 0 = x 0)
    (hrec : ∀ k i, v (k + 1) i = vhat W v k i + x (k + 1) i - x k i) :
    ∀ k i, yavg v k - vhat W v k i = ∑ l, (1 / (N : ℝ) - Phi W 0 k i l) • x 0 l +
      ∑ s ∈ Finset.Icc 1 k, ∑ j, (1 / (N : ℝ) - Phi W s (k - s) i j) •
        (x s j - x (s - 1) j) := by
  intro k i
  rw [yavg_repr hN W x v hcol hinit hrec k, vhat_repr W x v hinit hrec k i]
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

/-- the norm estimate (16) for a general increment bound -/
lemma disagreement_bound {N n : ℕ} (hN : 0 < N) (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (x v : ℕ → Fin N → E n)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hinit : v 0 = x 0)
    (hrec : ∀ k i, v (k + 1) i = vhat W v k i + x (k + 1) i - x k i)
    (θ β : ℝ) (hmix : ∀ s m i j, |Phi W s m i j - 1 / (N : ℝ)| ≤ θ * β ^ m)
    (M : ℝ) (hM : ∑ l, ‖x 0 l‖ ≤ M) (D : ℕ → ℝ)
    (hD : ∀ s j, 1 ≤ s → ‖x s j - x (s - 1) j‖ ≤ D s) (hθ : 0 ≤ θ) (hβ : 0 ≤ β) :
    ∀ k i, ‖yavg v k - vhat W v k i‖ ≤ θ * β ^ k * M +
      θ * (N : ℝ) * ∑ s ∈ Finset.Icc 1 k, β ^ (k - s) * D s := by
  intro k i
  rw [disagreement_repr hN W x v hcol hinit hrec k i]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    have : ∀ l ∈ Finset.univ, ‖(1 / (N : ℝ) - Phi W 0 k i l) • x 0 l‖ ≤
        θ * β ^ k * ‖x 0 l‖ := by
      intro l _
      rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (hmix 0 k i l) (norm_nonneg _)
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hM (by positivity)
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hs1 : 1 ≤ s := (Finset.mem_Icc.1 hs).1
    refine (norm_sum_le _ _).trans ?_
    have : ∀ j ∈ Finset.univ, ‖(1 / (N : ℝ) - Phi W s (k - s) i j) • (x s j - x (s - 1) j)‖ ≤
        θ * β ^ (k - s) * D s := by
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul (hmix s (k - s) i j) (hD s j hs1) (norm_nonneg _) (by positivity)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

end AggGameNet.Sync.L4aux

open AggGameNet.Sync AggGameNet.Sync.L4aux

theorem solution {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (hα : ∀ k, 0 ≤ α k)
    (x v : ℕ → Fin N → E n)
    (hrun : IsSyncRun K F W α x v)
    (C : ℝ)
    (hC : ∀ i k, ‖F i (x k i) ((N : ℝ) • vhat W v k i)‖ ≤ C)
    (M : ℝ)
    (hM : ∀ y : Fin N → E n, (∀ j, y j ∈ K j) → ∑ j, ‖y j‖ ≤ M) :
    ∀ i k, 1 ≤ k →
      ‖yavg v k - vhat W v k i‖ ≤
        theta N δ * beta N Q δ ^ k * M +
        theta N δ * (N : ℝ) * C *
          (∑ s ∈ Finset.Icc 1 k, beta N Q δ ^ (k - s) * α (s - 1)) := by
  intro i k _
  have hmix := (lemma_1 hN G Q h4 W δ hδ h5).2
  have hcol : ∀ k i, ∑ j, W k j i = 1 := fun k i => (h5 k).2.2 i
  have hfeas : ∀ k i, x k i ∈ K i := by
    intro k i
    cases k with
    | zero => exact hrun.1 i
    | succ k => exact ((hrun.2.2 k i).1).1
  -- θ ≥ 0, β ≥ 0
  have hbase : 0 < 1 - δ / (4 * (N : ℝ) ^ 2) := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hδ1 : δ ≤ 1 := by
      have hW0 : ∀ j, 0 ≤ W 0 ⟨0, hN⟩ j := by
        intro j
        by_cases hj : nbr G 0 ⟨0, hN⟩ j
        · exact hδ.le.trans (((h5 0).1 _ j).1 hj)
        · exact le_of_eq (((h5 0).1 _ j).2 hj).symm
      have hdiag : δ ≤ W 0 ⟨0, hN⟩ ⟨0, hN⟩ := ((h5 0).1 _ _).1 (Or.inl rfl)
      have hle : W 0 ⟨0, hN⟩ ⟨0, hN⟩ ≤ ∑ j, W 0 ⟨0, hN⟩ j :=
        Finset.single_le_sum (f := fun j => W 0 ⟨0, hN⟩ j) (fun j _ => hW0 j)
          (Finset.mem_univ _)
      rw [(h5 0).2.1] at hle
      linarith
    have : δ / (4 * (N : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hθ : 0 ≤ theta N δ := by unfold theta; positivity
  have hβ : 0 ≤ beta N Q δ := by unfold beta; exact Real.rpow_nonneg hbase.le _
  have hD : ∀ s j, 1 ≤ s → ‖x s j - x (s - 1) j‖ ≤ C * α (s - 1) := by
    intro s j hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hp := (hrun.2.2 t j).1
    have := isProj_dist_le ((h1.1 j).2.2) hp (x t j) (hfeas t j)
    refine this.trans ?_
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα t),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hC j t) (hα t)
  have hb := disagreement_bound hN W x v hcol hrun.2.1 (fun k i => (hrun.2.2 k i).2)
    (theta N δ) (beta N Q δ) hmix M (hM (x 0) (hfeas 0)) (fun s => C * α (s - 1)) hD hθ hβ k i
  refine hb.trans (le_of_eq ?_)
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => by ring)
