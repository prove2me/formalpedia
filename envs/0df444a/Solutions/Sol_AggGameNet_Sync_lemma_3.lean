-- Prove2me | solution 1 for AggGameNet.Sync.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:30:35.957401+00:00
-- url     : https://prove2.me/submissions/c7672d22-8c2a-44c1-b53d-0a4a85e5113f

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_AggGameNet_Sync_lemma_1
import Theorems.Thm_AggGameNet_Sync_lemma_2

namespace AggGameNet.Sync.L3aux

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

end AggGameNet.Sync.L3aux

open AggGameNet.Sync AggGameNet.Sync.L3aux

theorem solution {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (x v : ℕ → Fin N → E n)
    (hrun : IsSyncRun K F W α x v) :
    ∃ C : ℝ, ∀ i k,
      ‖F i (x k i) ((N : ℝ) • yavg v k)‖ ≤ C ∧
      ‖F i (x k i) ((N : ℝ) • vhat W v k i)‖ ≤ C := by
  have hmix := (lemma_1 hN G Q h4 W δ hδ h5).2
  have hcol : ∀ k i, ∑ j, W k j i = 1 := fun k i => (h5 k).2.2 i
  have hfeas : ∀ k i, x k i ∈ K i := by
    intro k i
    cases k with
    | zero => exact hrun.1 i
    | succ k => exact ((hrun.2.2 k i).1).1
  have hmean := lemma_2 hN W x v hcol hrun.2.1 (fun k i => (hrun.2.2 k i).2)
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNy : ∀ k, (N : ℝ) • yavg v k = ∑ j, x k j := by
    intro k
    rw [hmean k, smul_smul, mul_one_div_cancel hNne, one_smul]
  -- θ ≥ 0 and 0 ≤ β < 1
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
  have hβ0 : 0 ≤ beta N Q δ := (Real.rpow_pos_of_pos hbase0 _).le
  have hβ1 : beta N Q δ < 1 := Real.rpow_lt_one hbase0.le hbase1 hQ
  have hθ : 0 ≤ theta N δ := by unfold theta; positivity
  set β := beta N Q δ with hβdef
  set θ := theta N δ with hθdef
  -- bounds from compactness
  have hP : IsCompact (Set.univ.pi K) := isCompact_univ_pi (fun i => (h1.1 i).2.1)
  have hKbar : IsCompact (Kbar K) := by
    have : Kbar K = (fun y : Fin N → E n => ∑ i, y i) '' (Set.univ.pi K) := by
      ext u
      simp only [Kbar, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ_pi]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    rw [this]
    exact hP.image (continuous_finsetSum _ (fun i _ => continuous_apply i))
  obtain ⟨M1, hM10, hM1⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ a ∈ K i, ‖a‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_iUnion (fun i => (h1.1 i).2.1)).exists_bound_of_continuousOn
      (continuousOn_id (s := ⋃ i, K i))
    refine ⟨max M 0, le_max_right _ _, fun i a ha => ?_⟩
    have := hM a (Set.mem_iUnion.2 ⟨i, ha⟩)
    simp only [id] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨Fmax, hF⟩ : ∃ Fmax : ℝ, ∀ i, ∀ xi ∈ K i, ∀ u ∈ Kbar K, ‖F i xi u‖ ≤ Fmax := by
    have hb : ∀ i, ∃ Ci : ℝ, ∀ q ∈ K i ×ˢ Kbar K, ‖F i q.1 q.2‖ ≤ Ci := fun i =>
      (((h1.1 i).2.1).prod hKbar).exists_bound_of_continuousOn (h1.2 i)
    choose Ci hCi using hb
    refine ⟨∑ i, max (Ci i) 0, fun i xi hxi u hu => ?_⟩
    have h := hCi i (xi, u) ⟨hxi, hu⟩
    have : max (Ci i) 0 ≤ ∑ j, max (Ci j) 0 :=
      Finset.single_le_sum (f := fun j => max (Ci j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_univ i)
    exact h.trans ((le_max_left _ _).trans this)
  have hyK : ∀ k, (N : ℝ) • yavg v k ∈ Kbar K := fun k =>
    ⟨x k, hfeas k, hNy k⟩
  -- uniform disagreement bound
  set B : ℝ := θ * (N * M1) + θ * N * (2 * M1 * (1 - β)⁻¹) with hBdef
  have hB0 : 0 ≤ B := by
    have : 0 < 1 - β := by linarith
    positivity
  have hdis : ∀ k i, ‖yavg v k - vhat W v k i‖ ≤ B := by
    intro k i
    have hD : ∀ s j, 1 ≤ s → ‖x s j - x (s - 1) j‖ ≤ 2 * M1 := by
      intro s j _
      have := norm_sub_le (x s j) (x (s - 1) j)
      have := hM1 j _ (hfeas s j)
      have := hM1 j _ (hfeas (s - 1) j)
      linarith
    have hM0 : ∑ l, ‖x 0 l‖ ≤ N * M1 := by
      have := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hM1 l _ (hfeas 0 l))
      simpa using this
    have hb := disagreement_bound hN W x v hcol hrun.2.1 (fun k i => (hrun.2.2 k i).2)
      θ β hmix (N * M1) hM0 (fun _ => 2 * M1) hD hθ hβ0 k i
    refine hb.trans ?_
    have hgeo : ∑ s ∈ Finset.Icc 1 k, β ^ (k - s) ≤ (1 - β)⁻¹ := by
      have e : ∑ s ∈ Finset.Icc 1 k, β ^ (k - s) = ∑ t ∈ Finset.range k, β ^ t := by
        have : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
          ext s; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [this, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
        rw [← Finset.sum_range_reflect (fun t => β ^ t) k]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        congr 1
        omega
      rw [e, ← tsum_geometric_of_lt_one hβ0 hβ1]
      exact (summable_geometric_of_lt_one hβ0 hβ1).sum_le_tsum _ (fun t _ => pow_nonneg hβ0 _)
    have hpk : β ^ k ≤ 1 := pow_le_one₀ hβ0 hβ1.le
    have h2 : ∑ s ∈ Finset.Icc 1 k, β ^ (k - s) * (2 * M1) ≤ 2 * M1 * (1 - β)⁻¹ := by
      rw [← Finset.sum_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left hgeo (by positivity)
    have h3' : θ * β ^ k * (N * M1) ≤ θ * (N * M1) := by
      have := mul_le_mul_of_nonneg_left hpk hθ
      have : 0 ≤ (N : ℝ) * M1 := by positivity
      nlinarith
    have h4' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ θ * N)
    simp only [hBdef]
    linarith
  set Ls : ℝ := ∑ i, Lbar i with hLs
  have hLi : ∀ i, Lbar i ≤ Ls := fun i =>
    Finset.single_le_sum (f := Lbar) (fun j _ => (h3.1 j).le) (Finset.mem_univ i)
  have hLs0 : 0 ≤ Ls := Finset.sum_nonneg (fun j _ => (h3.1 j).le)
  refine ⟨Fmax + Ls * N * B, fun i k => ⟨?_, ?_⟩⟩
  · have := hF i _ (hfeas k i) _ (hyK k)
    have : 0 ≤ Ls * N * B := by positivity
    linarith
  · have hlip := h3.2 i (x k i) (hfeas k i) ((N : ℝ) • vhat W v k i) ((N : ℝ) • yavg v k)
    rw [← smul_sub, norm_smul, Real.norm_natCast] at hlip
    have hy := hF i _ (hfeas k i) _ (hyK k)
    have htri := norm_le_insert' (F i (x k i) ((N : ℝ) • vhat W v k i))
      (F i (x k i) ((N : ℝ) • yavg v k))
    have hd := hdis k i
    have e1 : Lbar i * (N * ‖yavg v k - vhat W v k i‖) ≤ Ls * N * B := by
      have := mul_le_mul hd (le_refl (N : ℝ)) (by positivity) hB0
      calc Lbar i * (N * ‖yavg v k - vhat W v k i‖)
          ≤ Lbar i * (B * N) := mul_le_mul_of_nonneg_left (by linarith) (h3.1 i).le
        _ ≤ Ls * (B * N) := mul_le_mul_of_nonneg_right (hLi i) (by positivity)
        _ = Ls * N * B := by ring
    rw [norm_sub_rev (yavg v k)] at e1
    linarith
