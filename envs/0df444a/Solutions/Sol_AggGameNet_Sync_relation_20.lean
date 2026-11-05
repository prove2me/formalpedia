-- Prove2me | solution 1 for AggGameNet.Sync.relation_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:26:30.174455+00:00
-- url     : https://prove2.me/submissions/e3f18806-b15b-4322-ade9-fbb913434ee8

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_AggGameNet_Sync_lemma_3
import Theorems.Thm_AggGameNet_Sync_lemma_4
import Theorems.Thm_AggGameNet_Sync_lemma_6

open AggGameNet.Sync
open Filter

theorem solution {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (h6 : Assumption6 α)
    (x v : ℕ → Fin N → E n) (hrun : IsSyncRun K F W α x v) :
    ∀ i, Summable (fun k => α k * ‖vhat W v k i - yavg v k‖) := by
  intro i
  obtain ⟨hanti, hdiv, hsq⟩ := h6
  -- nonnegativity of the steps
  have hα : ∀ k, 0 ≤ α k := by
    intro k
    by_contra hk
    push Not at hk
    have hb : ∀ T : ℕ, ∑ j ∈ Finset.range (k + T), α j ≤
        ∑ j ∈ Finset.range k, α j + T * α k := by
      intro T
      induction T with
      | zero => simp
      | succ T ih =>
        rw [← add_assoc, Finset.sum_range_succ]
        have : α (k + T) ≤ α k := hanti (Nat.le_add_right k T)
        push_cast; linarith
    have hev := hdiv.eventually (eventually_ge_atTop (∑ j ∈ Finset.range k, α j + 1))
    obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
    have e1 := hT0 (k + T0) (by omega)
    have e2 := hb T0
    have e3 : (T0 : ℝ) * α k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk.le
    linarith
  -- the constant C of Lemma 3
  obtain ⟨C, hC⟩ := lemma_3 hN K F h1 Lbar h3 G Q h4 W δ hδ h5 α x v hrun
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC ⟨0, hN⟩ 0).2
  -- the constant M
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ y : Fin N → E n, (∀ j, y j ∈ K j) → ∑ j, ‖y j‖ ≤ M := by
    have hb : ∀ j, ∃ Mj : ℝ, ∀ a ∈ K j, ‖a‖ ≤ Mj := fun j => by
      obtain ⟨Mj, hMj⟩ := ((h1.1 j).2.1).exists_bound_of_continuousOn
        (continuousOn_id (s := K j))
      exact ⟨Mj, fun a ha => by simpa using hMj a ha⟩
    choose Mj hMj using hb
    refine ⟨∑ j, max (Mj j) 0, Finset.sum_nonneg (fun j _ => le_max_right _ _),
      fun y hy => Finset.sum_le_sum (fun j _ => (hMj j (y j) (hy j)).trans (le_max_left _ _))⟩
  have hL4 := lemma_4 hN K F h1 Lbar h3 G Q h4 W δ hδ h5 α hα x v hrun C
    (fun i k => (hC i k).2) M hM
  -- 0 < β < 1 and θ > 0
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
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase0 : 0 < 1 - δ / (4 * (N : ℝ) ^ 2) := by
    have : δ / (4 * (N : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hbase1 : 1 - δ / (4 * (N : ℝ) ^ 2) < 1 := by
    have : 0 < δ / (4 * (N : ℝ) ^ 2) := by positivity
    linarith
  have hQ : (0 : ℝ) < 1 / (Q : ℝ) := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast h4.1
    positivity
  have hβ0 : 0 < beta N Q δ := Real.rpow_pos_of_pos hbase0 _
  have hβ1 : beta N Q δ < 1 := Real.rpow_lt_one hbase0.le hbase1 hQ
  have hθ0 : 0 < theta N δ := by unfold theta; positivity
  set β := beta N Q δ with hβdef
  set θ := theta N δ with hθdef
  -- Lemma 6 with ζ = α²
  have hg := lemma_6 (fun k => α k ^ 2) (fun k => sq_nonneg _) hsq β hβ0 hβ1
  have hgeom : Summable (fun m : ℕ => β ^ (m + 1)) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).comp_injective (add_left_injective 1)
  -- shifted bound
  apply (summable_nat_add_iff 1).1
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hα _) (norm_nonneg _)) (fun m => ?_)
    ((hgeom.mul_left (θ * M * α 0)).add (hg.mul_left (θ * N * C)))
  have hb := hL4 i (m + 1) (by omega)
  rw [norm_sub_rev] at hb
  have hsum_eq : ∑ s ∈ Finset.Icc 1 (m + 1), β ^ (m + 1 - s) * α (s - 1) =
      ∑ t ∈ Finset.range (m + 1), β ^ (m - t) * α t := by
    have : Finset.Icc 1 (m + 1) = Finset.Ico 1 (m + 2) := by
      ext s; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1) (fun t _ => ?_)
    have e1 : m + 1 - (1 + t) = m - t := by omega
    have e2 : 1 + t - 1 = t := by omega
    rw [e1, e2]
  rw [hsum_eq] at hb
  have hconv : α (m + 1) * ∑ t ∈ Finset.range (m + 1), β ^ (m - t) * α t ≤
      ∑ t ∈ Finset.range (m + 1), β ^ (m - t) * α t ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun t ht => ?_)
    have hle : α (m + 1) ≤ α t := hanti (by simp only [Finset.mem_range] at ht; omega)
    have := hα (m + 1)
    have := hα t
    have hp : 0 ≤ β ^ (m - t) := pow_nonneg hβ0.le _
    calc α (m + 1) * (β ^ (m - t) * α t) = β ^ (m - t) * (α (m + 1) * α t) := by ring
      _ ≤ β ^ (m - t) * (α t * α t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (hα t)) hp
      _ = β ^ (m - t) * α t ^ 2 := by ring
  have hαm := hα (m + 1)
  have hα0 : α (m + 1) ≤ α 0 := hanti (Nat.zero_le _)
  have hβp : 0 ≤ β ^ (m + 1) := pow_nonneg hβ0.le _
  have hS0 : 0 ≤ ∑ t ∈ Finset.range (m + 1), β ^ (m - t) * α t :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (pow_nonneg hβ0.le _) (hα t))
  have hk := mul_le_mul_of_nonneg_left hb hαm
  have t1 : α (m + 1) * (θ * β ^ (m + 1) * M) ≤ θ * M * α 0 * β ^ (m + 1) := by
    have := mul_le_mul_of_nonneg_right hα0 (by positivity : 0 ≤ θ * β ^ (m + 1) * M)
    linarith
  have t2 : α (m + 1) * (θ * N * C * ∑ t ∈ Finset.range (m + 1), β ^ (m - t) * α t) ≤
      θ * N * C * ∑ t ∈ Finset.range (m + 1), β ^ (m - t) * α t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hconv (by positivity : 0 ≤ θ * N * C)
    linarith
  show _ ≤ θ * M * α 0 * β ^ (m + 1) + θ * N * C * _
  linarith
