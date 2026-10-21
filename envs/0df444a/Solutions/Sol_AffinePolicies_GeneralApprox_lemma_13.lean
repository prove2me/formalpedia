-- Prove2me | solution 1 for AffinePolicies.GeneralApprox.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:58:12.30038+00:00
-- url     : https://prove2.me/submissions/b6fde805-ba70-48e9-b068-c1760511af94

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

set_option autoImplicit false
open Matrix Filter Topology
open AffinePolicies.SqrtBound AffinePolicies.GeneralApprox AffinePolicies.Simplex

lemma apg_mu_pos {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUfull : (interior U).Nonempty) (μ : Fin m → ℝ)
    (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j)) : ∀ j, 0 < μ j := by
  intro j
  obtain ⟨b0, hb0⟩ := hUfull
  have hU : U ∈ 𝓝 b0 := mem_interior_iff_mem_nhds.1 hb0
  have hcont : Continuous (fun t : ℝ => b0 + t • (Pi.single j (1 : ℝ) : Fin m → ℝ)) := by
    fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), b0 + t • (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  have h1 := (hμ j).2 ⟨_, ht, rfl⟩
  have h2 : 0 ≤ b0 j := hUnn b0 (interior_subset hb0) j
  simp at h1
  have : (0 : ℝ) < t := htpos
  linarith

lemma apg_alg {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (K : ℕ) (u : ℕ → Fin m → ℝ)
    (hu0 : ∀ i, 1 ≤ i → i ≤ K → ∀ j, 0 ≤ u i j) :
    ∀ k ≤ K, ∀ j, (j ∉ J1 μ u k → μ j ≤ bvec μ u k j) ∧
      bvec μ u k j ≤ ∑ i ∈ Finset.Icc 1 k, u i j := by
  intro k
  induction k with
  | zero => intro _ j; simp [J1, bvec, algState]
  | succ k ih =>
    intro hk j
    have ih' := ih (by omega) j
    have hu : 0 ≤ u (k + 1) j := hu0 (k + 1) (by omega) hk j
    have hb : bvec μ u (k + 1) j =
        if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := rfl
    have hJ : J1 μ u (k + 1) = (J1 μ u k).filter (fun j =>
        (if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j) < μ j) := rfl
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    constructor
    · intro hj
      rw [hJ, Finset.mem_filter] at hj
      rw [hb]
      by_cases hjk : j ∈ J1 μ u k
      · simp only [hjk, true_and, if_true] at hj ⊢
        exact not_lt.mp hj
      · simp only [hjk, if_false]
        exact ih'.1 hjk
    · rw [hb]
      by_cases hjk : j ∈ J1 μ u k
      · simp only [hjk, if_true]
        linarith [ih'.2]
      · simp only [hjk, if_false]
        linarith [ih'.2]

lemma apg_lemma12 {m : ℕ} (U : Set (Fin m → ℝ))
    (hUnn : ∀ b ∈ U, 0 ≤ b) (hUfull : (interior U).Nonempty)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u) :
    ∀ b ∈ U, ∃ b' ∈ U0 bstar u K, b ≤ b' := by
  intro b hb
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    exact ⟨(2 : ℝ) • betaSum u K, subset_convexHull ℝ _ (Or.inr rfl), fun i => i.elim0⟩
  have hμpos := apg_mu_pos U hUnn hUfull μ hμ
  have hsqpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  obtain ⟨hiter, hnoloop⟩ := hrun
  have hu0 : ∀ i, 1 ≤ i → i ≤ K → ∀ j, 0 ≤ u i j := by
    intro i hi1 hiK j
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hUnn _ (hiter i' (by omega)).2.1 j
  have halg := apg_alg U μ K u hu0 K le_rfl
  have hbJ : ∑ j ∈ J1 μ u K, b j / μ j ≤ Real.sqrt m := by
    unfold LoopCond at hnoloop
    push Not at hnoloop
    exact hnoloop b hb
  have hβ : ∀ i, betaSum u K i = ∑ k ∈ Finset.Icc 1 K, u k i := by
    intro i; simp [betaSum, Finset.sum_apply]
  have hβ0 : ∀ i, 0 ≤ betaSum u K i := by
    intro i; rw [hβ]
    exact Finset.sum_nonneg (fun k hk => hu0 k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2 i)
  have hbμ : ∀ j, b j ≤ μ j := fun j => (hμ j).2 ⟨b, hb, rfl⟩
  have hJ2 : ∀ j, j ∉ J1 μ u K → μ j ≤ betaSum u K j := fun j hj => by
    rw [hβ]; exact le_trans ((halg j).1 hj) (halg j).2
  -- weights
  set w : Fin m → ℝ := fun j => if j ∈ J1 μ u K then b j / (2 * Real.sqrt m * μ j) else 0 with hw
  have hbnn : ∀ j, 0 ≤ b j := fun j => hUnn b hb j
  have hbsnn : ∀ j i, 0 ≤ bstar j i := fun j i => hUnn _ (hbstar j).1 i
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    simp only [hw]
    split_ifs
    · have := hbnn j
      have := hμpos j
      positivity
    · exact le_rfl
  have hwsum : ∑ j, w j ≤ 1 / 2 := by
    have : ∑ j, w j = (∑ j ∈ J1 μ u K, b j / μ j) / (2 * Real.sqrt m) := by
      simp only [hw]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := (hμpos j).ne'
      field_simp
    rw [this, div_le_iff₀ (by positivity)]
    linarith
  -- the point b'
  let ω : Option (Fin m) → ℝ := fun o => match o with
    | none => 1 - ∑ j, w j
    | some j => w j
  let z : Option (Fin m) → (Fin m → ℝ) := fun o => match o with
    | none => (2 : ℝ) • betaSum u K
    | some j => (2 * Real.sqrt m) • bstar j
  have hω0 : ∀ o, 0 ≤ ω o := by
    intro o
    cases o with
    | none => show 0 ≤ 1 - ∑ j, w j; linarith
    | some j => exact hw0 j
  have hω1 : ∑ o, ω o = 1 := by
    rw [Fintype.sum_option]
    show (1 - ∑ j, w j) + ∑ j, w j = 1
    ring
  have hzmem : ∀ o, z o ∈ U0 bstar u K := by
    intro o
    cases o with
    | none => exact subset_convexHull ℝ _ (Or.inr rfl)
    | some j => exact subset_convexHull ℝ _ (Or.inl ⟨j, rfl⟩)
  have hmem : ∑ o, ω o • z o ∈ U0 bstar u K :=
    (convex_convexHull ℝ _).sum_mem (fun o _ => hω0 o) (by simpa using hω1) (fun o _ => hzmem o)
  refine ⟨_, hmem, fun i => ?_⟩
  have hcoord : (∑ o, ω o • z o) i = (1 - ∑ j, w j) * (2 * betaSum u K i) +
      ∑ j, w j * ((2 * Real.sqrt m) * bstar j i) := by
    rw [Fintype.sum_option]
    simp [ω, z, Finset.sum_apply]
  rw [hcoord]
  have hA : 0 ≤ (1 - ∑ j, w j) * (2 * betaSum u K i) := by
    have := hβ0 i
    have : 0 ≤ 1 - ∑ j, w j := by linarith
    positivity
  have hS : ∀ j, 0 ≤ w j * ((2 * Real.sqrt m) * bstar j i) := fun j => by
    have := hbsnn j i
    have := hw0 j
    positivity
  by_cases hi : i ∈ J1 μ u K
  · have h1 : w i * ((2 * Real.sqrt m) * bstar i i) ≤ ∑ j, w j * ((2 * Real.sqrt m) * bstar j i) :=
      Finset.single_le_sum (f := fun j => w j * ((2 * Real.sqrt m) * bstar j i))
        (fun j _ => hS j) (Finset.mem_univ i)
    have h2 : w i * ((2 * Real.sqrt m) * bstar i i) = b i := by
      simp only [hw, hi, if_true, (hbstar i).2]
      have := (hμpos i).ne'
      field_simp
    linarith
  · have h1 := hJ2 i hi
    have h2 := hbμ i
    have h3 : 0 ≤ ∑ j, w j * ((2 * Real.sqrt m) * bstar j i) := Finset.sum_nonneg (fun j _ => hS j)
    have h4 : betaSum u K i ≤ (1 - ∑ j, w j) * (2 * betaSum u K i) := by
      have := hβ0 i
      nlinarith
    linarith

lemma apg_construct {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ)) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hUnn : ∀ b ∈ U, 0 ≤ b)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (huU : ∀ k, 1 ≤ k → k ≤ K → u k ∈ U)
    (hK : (K : ℝ) ≤ 2 * Real.sqrt m)
    (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (hx : 0 ≤ x)
    (hfeas : ∀ b ∈ U, 0 ≤ y b ∧ b ≤ A *ᵥ x + B *ᵥ y b)
    (b0 : Fin m → ℝ) (hb0 : b0 ∈ U) (t0 : ℝ)
    (hcb : ∀ j, c ⬝ᵥ x + d ⬝ᵥ y (bstar j) ≤ t0)
    (hcu : ∀ k, 1 ≤ k → k ≤ K → c ⬝ᵥ x + d ⬝ᵥ y (u k) ≤ t0)
    (hc0 : c ⬝ᵥ x + d ⬝ᵥ y b0 ≤ t0) :
    ∃ y' : (Fin m → ℝ) → Fin n₂ → ℝ, Feasible A B (U0 bstar u K) ((4 * Real.sqrt m) • x) y' ∧
      CostLE c d (U0 bstar u K) ((4 * Real.sqrt m) • x) y' (4 * Real.sqrt m * t0) := by
  classical
  set r : ℝ := 4 * Real.sqrt m with hr
  have hsq0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  let Good : (Fin m → ℝ) → Prop := fun b' => ∃ y' : Fin n₂ → ℝ, 0 ≤ y' ∧
    b' ≤ A *ᵥ (r • x) + B *ᵥ y' ∧ c ⬝ᵥ (r • x) + d ⬝ᵥ y' ≤ r * t0
  have hconv : Convex ℝ {b' | Good b'} := by
    intro b1 hb1 b2 hb2 a b ha hb hab
    obtain ⟨y1, hy1, hl1, hc1⟩ := hb1
    obtain ⟨y2, hy2, hl2, hc2⟩ := hb2
    refine ⟨a • y1 + b • y2, add_nonneg (smul_nonneg ha hy1) (smul_nonneg hb hy2), ?_, ?_⟩
    · have key : ∀ v w1 w2 : Fin m → ℝ, v + (a • w1 + b • w2) = a • (v + w1) + b • (v + w2) := by
        intro v w1 w2
        have hv : v = a • v + b • v := by rw [← add_smul, hab, one_smul]
        calc v + (a • w1 + b • w2) = (a • v + b • v) + (a • w1 + b • w2) := by rw [← hv]
          _ = a • (v + w1) + b • (v + w2) := by simp only [smul_add]; abel
      have hB : B *ᵥ (a • y1 + b • y2) = a • (B *ᵥ y1) + b • (B *ᵥ y2) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      rw [hB, key]
      exact add_le_add (smul_le_smul_of_nonneg_left hl1 ha) (smul_le_smul_of_nonneg_left hl2 hb)
    · obtain rfl : b = 1 - a := by linarith
      have e : c ⬝ᵥ (r • x) + d ⬝ᵥ (a • y1 + (1 - a) • y2) =
          a * (c ⬝ᵥ (r • x) + d ⬝ᵥ y1) + (1 - a) * (c ⬝ᵥ (r • x) + d ⬝ᵥ y2) := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        ring
      rw [e]
      nlinarith
  have hgen1 : ∀ j, Good ((2 * Real.sqrt m) • bstar j) := by
    intro j
    obtain ⟨hy, hfe⟩ := hfeas _ (hbstar j)
    refine ⟨r • y (bstar j), smul_nonneg hr0 hy, ?_, ?_⟩
    · have h1 : A *ᵥ (r • x) + B *ᵥ (r • y (bstar j)) = r • (A *ᵥ x + B *ᵥ y (bstar j)) := by
        simp [Matrix.mulVec_smul, smul_add]
      rw [h1]
      calc (2 * Real.sqrt m) • bstar j ≤ r • bstar j :=
            smul_le_smul_of_nonneg_right (by rw [hr]; linarith) (hUnn _ (hbstar j))
        _ ≤ r • (A *ᵥ x + B *ᵥ y (bstar j)) := smul_le_smul_of_nonneg_left hfe hr0
    · have e : c ⬝ᵥ (r • x) + d ⬝ᵥ (r • y (bstar j)) = r * (c ⬝ᵥ x + d ⬝ᵥ y (bstar j)) := by
        rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (hcb j) hr0
  have hβ0 : 0 ≤ betaSum u K := Finset.sum_nonneg (fun k hk =>
    hUnn _ (huU k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2))
  have hgen2 : Good ((2 : ℝ) • betaSum u K) := by
    by_cases hK0 : K = 0
    · subst hK0
      have : betaSum u 0 = 0 := by simp [betaSum]
      rw [this, smul_zero]
      obtain ⟨hy, hfe⟩ := hfeas _ hb0
      refine ⟨r • y b0, smul_nonneg hr0 hy, ?_, ?_⟩
      · have h1 : A *ᵥ (r • x) + B *ᵥ (r • y b0) = r • (A *ᵥ x + B *ᵥ y b0) := by
          simp [Matrix.mulVec_smul, smul_add]
        rw [h1]
        calc (0 : Fin m → ℝ) ≤ r • b0 := smul_nonneg hr0 (hUnn _ hb0)
          _ ≤ r • (A *ᵥ x + B *ᵥ y b0) := smul_le_smul_of_nonneg_left hfe hr0
      · have e : c ⬝ᵥ (r • x) + d ⬝ᵥ (r • y b0) = r * (c ⬝ᵥ x + d ⬝ᵥ y b0) := by
          rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hc0 hr0
    · have Kpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
      set Y : Fin n₂ → ℝ := ∑ k ∈ Finset.Icc 1 K, y (u k) with hY
      have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun k hk =>
        (hfeas _ (huU k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)).1)
      refine ⟨(r / K) • Y, smul_nonneg (by positivity) hY0, ?_, ?_⟩
      · have hsumle : betaSum u K ≤ ∑ k ∈ Finset.Icc 1 K, (A *ᵥ x + B *ᵥ y (u k)) :=
          Finset.sum_le_sum (fun k hk =>
            (hfeas _ (huU k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)).2)
        have hE : ∑ k ∈ Finset.Icc 1 K, (A *ᵥ x + B *ᵥ y (u k)) =
            (K : ℝ) • (A *ᵥ x) + B *ᵥ Y := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
            ← Nat.cast_smul_eq_nsmul ℝ, ← Matrix.mulVec_sum]
        have hE2 : A *ᵥ (r • x) + B *ᵥ ((r / K) • Y) =
            (r / K) • ((K : ℝ) • (A *ᵥ x) + B *ᵥ Y) := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_add, smul_smul,
            div_mul_cancel₀ _ Kpos.ne']
        have h2 : (2 : ℝ) ≤ r / K := by
          rw [le_div_iff₀ Kpos, hr]; linarith
        rw [hE2, ← hE]
        calc (2 : ℝ) • betaSum u K ≤ (r / K) • betaSum u K :=
              smul_le_smul_of_nonneg_right h2 hβ0
          _ ≤ _ := smul_le_smul_of_nonneg_left hsumle (by positivity)
      · have hdY : d ⬝ᵥ Y = ∑ k ∈ Finset.Icc 1 K, d ⬝ᵥ y (u k) := by
          rw [hY, dotProduct_sum]
        have hsum : ∑ k ∈ Finset.Icc 1 K, (c ⬝ᵥ x + d ⬝ᵥ y (u k)) ≤ K * t0 := by
          calc _ ≤ ∑ k ∈ Finset.Icc 1 K, t0 := Finset.sum_le_sum (fun k hk =>
                hcu k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)
            _ = K * t0 := by simp
        have hsum2 : ∑ k ∈ Finset.Icc 1 K, (c ⬝ᵥ x + d ⬝ᵥ y (u k)) =
            K * (c ⬝ᵥ x) + d ⬝ᵥ Y := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, hdY]
          simp
        rw [hsum2] at hsum
        have e : c ⬝ᵥ (r • x) + d ⬝ᵥ ((r / K) • Y) = (r / K) * (K * (c ⬝ᵥ x) + d ⬝ᵥ Y) := by
          rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
          field_simp
        rw [e]
        calc (r / K) * (K * (c ⬝ᵥ x) + d ⬝ᵥ Y) ≤ (r / K) * (K * t0) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = r * t0 := by field_simp
  have hsub : U0 bstar u K ⊆ {b' | Good b'} := by
    refine convexHull_min ?_ hconv
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨j, rfl⟩; exact hgen1 j
    · rintro _ rfl; exact hgen2
  have hex : ∀ b ∈ U0 bstar u K, ∃ y' : Fin n₂ → ℝ, 0 ≤ y' ∧
      b ≤ A *ᵥ (r • x) + B *ᵥ y' ∧ c ⬝ᵥ (r • x) + d ⬝ᵥ y' ≤ r * t0 := fun b hb => hsub hb
  choose! y' hy' using hex
  exact ⟨y', ⟨smul_nonneg hr0 hx, fun b hb => ⟨(hy' b hb).1, (hy' b hb).2.1⟩⟩,
    fun b hb => (hy' b hb).2.2⟩


lemma apg_K_bound {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUfull : (interior U).Nonempty) (μ : Fin m → ℝ)
    (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) : (K : ℝ) ≤ 2 * Real.sqrt m := by
  have hμpos := apg_mu_pos U hUnn hUfull μ hμ
  obtain ⟨hiter, hnoloop⟩ := hrun
  set T : ℕ → ℝ := fun k => ∑ j, bvec μ u k j / μ j with hT
  have hstep : ∀ k, bvec μ u (k + 1) = fun j =>
      if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := fun k => rfl
  have hJstep : ∀ k, J1 μ u (k + 1) = (J1 μ u k).filter (fun j =>
      (if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j) < μ j) := fun k => rfl
  -- (i) potential grows
  have hgrow : ∀ k ≤ K, (k : ℝ) * Real.sqrt m ≤ T k := by
    intro k
    induction k with
    | zero => intro _; simp [hT, bvec, algState]
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      obtain ⟨hloop, huk, hmax⟩ := hiter k (by omega)
      obtain ⟨b, hbU, hb⟩ := hloop
      have h1 : Real.sqrt m < scaledSum μ (J1 μ u k) (u (k + 1)) := lt_of_lt_of_le hb (hmax b hbU)
      have h2 : T (k + 1) = T k + scaledSum μ (J1 μ u k) (u (k + 1)) := by
        simp only [hT, scaledSum, hstep]
        have : ∀ j, (if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j) / μ j =
            bvec μ u k j / μ j + (if j ∈ J1 μ u k then u (k + 1) j / μ j else 0) := by
          intro j
          by_cases hj : j ∈ J1 μ u k
          · simp only [hj, if_true]; ring
          · simp [hj]
        rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_mem,
          Finset.univ_inter]
      rw [h2]; push_cast; nlinarith
  -- (ii) iterates are bounded by 2 μ
  have hu_le : ∀ k, k < K → ∀ j, u (k + 1) j ≤ μ j := fun k hk j =>
    (hμ j).2 ⟨_, (hiter k hk).2.1, rfl⟩
  have hu0 : ∀ k, k < K → ∀ j, 0 ≤ u (k + 1) j := fun k hk j => hUnn _ (hiter k hk).2.1 j
  have hbd : ∀ k ≤ K, ∀ j, bvec μ u k j < 2 * μ j ∧ (j ∈ J1 μ u k → bvec μ u k j < μ j) := by
    intro k
    induction k with
    | zero => intro _ j; have := hμpos j; simp [bvec, J1, algState]; linarith
    | succ k ih =>
      intro hk j
      have ih' := ih (by omega) j
      have hul := hu_le k (by omega) j
      have hb : bvec μ u (k + 1) j =
          if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := rfl
      have hμj := hμpos j
      by_cases hjk : j ∈ J1 μ u k
      · have h1 := ih'.2 hjk
        have hbj : bvec μ u (k + 1) j = bvec μ u k j + u (k + 1) j := by rw [hb]; simp [hjk]
        refine ⟨by rw [hbj]; linarith, fun hj => ?_⟩
        rw [hJstep, Finset.mem_filter] at hj
        have := hj.2
        simp only [hjk, if_true] at this
        rw [hbj]; exact this
      · have hbj : bvec μ u (k + 1) j = bvec μ u k j := by rw [hb]; simp [hjk]
        refine ⟨by rw [hbj]; exact ih'.1, fun hj => ?_⟩
        rw [hJstep, Finset.mem_filter] at hj
        exact absurd hj.1 hjk
  have hTle : T K ≤ 2 * m := by
    have : ∀ j, bvec μ u K j / μ j ≤ 2 := fun j => by
      rw [div_le_iff₀ (hμpos j)]; linarith [(hbd K le_rfl j).1]
    calc T K ≤ ∑ _j : Fin m, (2 : ℝ) := Finset.sum_le_sum (fun j _ => this j)
      _ = 2 * m := by simp [mul_comm]
  have hK2 := hgrow K le_rfl
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0; simp
  · have hm : 0 < m := by
      by_contra hm0
      have hm0' : m = 0 := by omega
      subst hm0'
      obtain ⟨b, _, hb⟩ := (hiter 0 hKpos).1
      have h0 : scaledSum μ (J1 μ u 0) b = 0 := by
        unfold scaledSum; exact Finset.sum_eq_zero (fun j _ => j.elim0)
      rw [h0] at hb
      simp at hb
    have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have hsqsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (by positivity)
    have : (K : ℝ) * Real.sqrt m ≤ (2 * Real.sqrt m) * Real.sqrt m := by nlinarith
    exact le_of_mul_le_mul_right this hsq

theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUconv : Convex ℝ U) (hUcpt : IsCompact U) (hUfull : (interior U).Nonempty)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), AffinePolicies.Simplex.Feasible A B U x y)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u) :
    (∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ),
        AffinePolicies.Simplex.Feasible A B (U0 bstar u K) x y ∧ AffinePolicies.Simplex.CostLE c d (U0 bstar u K) x y t) ∧
      AffinePolicies.Simplex.zAdapt A B c d (U0 bstar u K) ≤ 4 * Real.sqrt m * AffinePolicies.Simplex.zAdapt A B c d U := by
  classical
  have hKb := apg_K_bound U hUnn hUfull μ hμ K u hrun
  have hdom := apg_lemma12 U hUnn hUfull μ hμ bstar hbstar K u hrun
  have huU : ∀ k, 1 ≤ k → k ≤ K → u k ∈ U := by
    intro k hk1 hkK
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact (hrun.1 k' (by omega)).2.1
  have hbs : ∀ j, bstar j ∈ U := fun j => (hbstar j).1
  obtain ⟨b0, hb0i⟩ := hUfull
  have hb0 : b0 ∈ U := interior_subset hb0i
  set r : ℝ := 4 * Real.sqrt m with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hdotnn : ∀ (v : Fin n₁ → ℝ) (w : Fin n₁ → ℝ), 0 ≤ v → 0 ≤ w → 0 ≤ v ⬝ᵥ w := by
    intro v w hv hw
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))
  have hdotnn2 : ∀ (v : Fin n₂ → ℝ) (w : Fin n₂ → ℝ), 0 ≤ v → 0 ≤ w → 0 ≤ v ⬝ᵥ w := by
    intro v w hv hw
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))
  -- general building step
  have hbuild : ∀ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (t0 : ℝ),
      0 ≤ x → (∀ b ∈ U, 0 ≤ y b ∧ b ≤ A *ᵥ x + B *ᵥ y b) →
      (∀ j, c ⬝ᵥ x + d ⬝ᵥ y (bstar j) ≤ t0) →
      (∀ k, 1 ≤ k → k ≤ K → c ⬝ᵥ x + d ⬝ᵥ y (u k) ≤ t0) → c ⬝ᵥ x + d ⬝ᵥ y b0 ≤ t0 →
      ∃ y' : (Fin m → ℝ) → Fin n₂ → ℝ, Feasible A B (U0 bstar u K) (r • x) y' ∧
        CostLE c d (U0 bstar u K) (r • x) y' (r * t0) := by
    intro x y t0 hx hf hcb hcu hc0
    exact apg_construct A B c d U hc hd hUnn bstar hbs K u huU hKb x y hx hf b0 hb0 t0 hcb hcu hc0
  -- bounded-cost solutions for U0 from a feasible solution of U
  have hcostnn : ∀ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), 0 ≤ x →
      (∀ b ∈ U, 0 ≤ y b ∧ b ≤ A *ᵥ x + B *ᵥ y b) → ∀ b ∈ U, 0 ≤ c ⬝ᵥ x + d ⬝ᵥ y b := by
    intro x y hx hf b hb
    exact add_nonneg (hdotnn c x hc hx) (hdotnn2 d _ hd (hf b hb).1)
  have hpart1 : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ),
      Feasible A B (U0 bstar u K) x y ∧ CostLE c d (U0 bstar u K) x y t := by
    obtain ⟨x0, y0, hx0, hf0⟩ := hfeas
    set cost : (Fin m → ℝ) → ℝ := fun b => c ⬝ᵥ x0 + d ⬝ᵥ y0 b with hcost
    have hcn := hcostnn x0 y0 hx0 hf0
    set t0 : ℝ := ∑ j, cost (bstar j) + ∑ k ∈ Finset.Icc 1 K, cost (u k) + cost b0 with ht0
    have hS1 : 0 ≤ ∑ j, cost (bstar j) := Finset.sum_nonneg (fun j _ => hcn _ (hbs j))
    have hS2 : 0 ≤ ∑ k ∈ Finset.Icc 1 K, cost (u k) := Finset.sum_nonneg (fun k hk =>
      hcn _ (huU k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2))
    have hS3 : 0 ≤ cost b0 := hcn _ hb0
    obtain ⟨y', hF, hC⟩ := hbuild x0 y0 t0 hx0 hf0
      (fun j => by
        have : cost (bstar j) ≤ ∑ j, cost (bstar j) :=
          Finset.single_le_sum (f := fun j => cost (bstar j)) (fun j _ => hcn _ (hbs j)) (Finset.mem_univ j)
        simp only [hcost] at this ht0 ⊢; linarith)
      (fun k hk1 hkK => by
        have : cost (u k) ≤ ∑ k ∈ Finset.Icc 1 K, cost (u k) :=
          Finset.single_le_sum (f := fun k => cost (u k))
            (fun k hk => hcn _ (huU k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2))
            (Finset.mem_Icc.2 ⟨hk1, hkK⟩)
        simp only [hcost] at this ht0 ⊢; linarith)
      (by simp only [hcost] at hS3 ht0 ⊢; linarith)
    exact ⟨_, y', _, hF, hC⟩
  refine ⟨hpart1, ?_⟩
  -- part 2
  set SU : Set ℝ := {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
    Feasible A B U x y ∧ CostLE c d U x y t} with hSU
  set SU0 : Set ℝ := {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
    Feasible A B (U0 bstar u K) x y ∧ CostLE c d (U0 bstar u K) x y t} with hSU0
  have hz : zAdapt A B c d U = sInf SU := rfl
  have hz0 : zAdapt A B c d (U0 bstar u K) = sInf SU0 := rfl
  have hmem0 : (2 : ℝ) • betaSum u K ∈ U0 bstar u K := subset_convexHull ℝ _ (Or.inr rfl)
  have hbdd : BddBelow SU0 := by
    refine ⟨0, ?_⟩
    rintro t ⟨x, y, hF, hC⟩
    have h1 := hC _ hmem0
    have h2 := add_nonneg (hdotnn c x hc hF.1) (hdotnn2 d _ hd (hF.2 _ hmem0).1)
    linarith
  -- each element of SU gives an element of SU0 scaled by r
  have hscale : ∀ t ∈ SU, r * t ∈ SU0 := by
    rintro t ⟨x, y, hF, hC⟩
    obtain ⟨y', hF', hC'⟩ := hbuild x y t hF.1 hF.2 (fun j => hC _ (hbs j))
      (fun k hk1 hkK => hC _ (huU k hk1 hkK)) (hC _ hb0)
    exact ⟨_, y', hF', hC'⟩
  -- SU is nonempty (domination by U0)
  have hne : SU.Nonempty := by
    obtain ⟨x0, y0, hx0, hf0⟩ := hfeas
    obtain ⟨x, y, t, hF, hC⟩ := hpart1
    -- x is r • x0 ; we only know existence, so rebuild from hpart1's data
    choose! f hfU hfle using hdom
    refine ⟨t, x, fun b => y (f b), ⟨hF.1, fun b hb => ⟨(hF.2 _ (hfU b hb)).1, ?_⟩⟩, fun b hb => hC _ (hfU b hb)⟩
    exact le_trans (hfle b hb) (hF.2 _ (hfU b hb)).2
  rw [hz, hz0]
  rcases hne with ⟨t1, ht1⟩
  have hup : ∀ t ∈ SU, sInf SU0 ≤ r * t := fun t ht => csInf_le hbdd (hscale t ht)
  rcases hr0.eq_or_lt with hr_eq | hr_pos
  · have := hup t1 ht1
    rw [← hr_eq] at this ⊢
    simpa using this
  · have hBddU : sInf SU0 / r ≤ sInf SU := by
      refine le_csInf ⟨t1, ht1⟩ (fun t ht => ?_)
      rw [div_le_iff₀ hr_pos, mul_comm]
      exact hup t ht
    rw [div_le_iff₀ hr_pos, mul_comm] at hBddU
    exact hBddU
