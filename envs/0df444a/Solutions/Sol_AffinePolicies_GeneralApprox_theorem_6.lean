-- Prove2me | solution 1 for AffinePolicies.GeneralApprox.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T23:57:38.858327+00:00
-- url     : https://prove2.me/submissions/4a501535-012d-4287-a582-7d1825d85484

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

set_option autoImplicit false

namespace P5a698ddd

open Matrix AffinePolicies.SqrtBound

lemma bvec_succ {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) (j : Fin m) :
    bvec μ u (k + 1) j =
      if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := rfl

lemma J1_succ {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) :
    J1 μ u (k + 1) = (J1 μ u k).filter (fun j => bvec μ u (k + 1) j < μ j) := rfl

lemma bvec_zero {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) : bvec μ u 0 = 0 := rfl

lemma J1_zero {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) : J1 μ u 0 = Finset.univ := rfl

lemma mu_pos' {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUfull : (interior U).Nonempty)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j)) :
    ∀ j, 0 < μ j := by
  intro j
  obtain ⟨x, hx⟩ := hUfull
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set y : Fin m → ℝ := x + (ε / 2) • Pi.single j (1 : ℝ) with hy
  have hyU : y ∈ U := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hy, add_sub_cancel_left, norm_smul,
      Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hxU : x ∈ U := interior_subset hx
  have h1 : y j ≤ μ j := (hμ j).2 ⟨y, hyU, rfl⟩
  have h2 : 0 ≤ x j := hUnn x hxU j
  have h3 : y j = x j + ε / 2 := by simp [hy]
  linarith

lemma u_mem {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (K : ℕ) (u : ℕ → Fin m → ℝ)
    (hrun : IsRun U μ K u) (k : ℕ) (hk : k < K) : u (k + 1) ∈ U :=
  (hrun.1 k hk).2.1

lemma bvec_le_sum {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b) (μ : Fin m → ℝ)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    ∀ k ≤ K, ∀ j, bvec μ u k j ≤ ∑ i ∈ Finset.Icc 1 k, u i j := by
  intro k
  induction k with
  | zero => intro _ j; simp [bvec_zero]
  | succ k ih =>
    intro hk j
    have h0 : 0 ≤ u (k + 1) j := hUnn _ (u_mem U μ K u hrun k (by omega)) j
    rw [Finset.sum_Icc_succ_top (by omega), bvec_succ]
    have := ih (by omega) j
    split_ifs <;> linarith

lemma ge_mu {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) :
    ∀ k, ∀ j, j ∉ J1 μ u k → μ j ≤ bvec μ u k j := by
  intro k
  induction k with
  | zero => intro j hj; simp [J1_zero] at hj
  | succ k ih =>
    intro j hj
    rw [J1_succ, Finset.mem_filter] at hj
    by_cases hjk : j ∈ J1 μ u k
    · simp only [not_and, not_lt] at hj
      exact hj hjk
    · rw [bvec_succ, if_neg hjk]
      exact ih j hjk

lemma inv_bound {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (hμpos : ∀ j, 0 < μ j)
    (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    ∀ k ≤ K, ∀ j, (j ∈ J1 μ u k → bvec μ u k j < μ j) ∧ bvec μ u k j ≤ 2 * μ j := by
  intro k
  induction k with
  | zero =>
    intro _ j
    have := hμpos j
    simp only [bvec_zero, Pi.zero_apply]
    constructor
    · intro _; linarith
    · linarith
  | succ k ih =>
    intro hk j
    have hu : u (k + 1) j ≤ μ j := hbμ _ (u_mem U μ K u hrun k (by omega)) j
    obtain ⟨h1, h2⟩ := ih (by omega) j
    constructor
    · intro hj
      rw [J1_succ, Finset.mem_filter] at hj
      exact hj.2
    · rw [bvec_succ]
      split_ifs with hjk
      · have := h1 hjk; linarith
      · exact h2

lemma sum_identity {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) :
    ∀ k, ∑ i ∈ Finset.range k, scaledSum μ (J1 μ u i) (u (i + 1)) =
      ∑ j, bvec μ u k j / μ j := by
  intro k
  induction k with
  | zero => simp [bvec_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have e : ∀ j, bvec μ u (k + 1) j / μ j =
        bvec μ u k j / μ j + (if j ∈ J1 μ u k then u (k + 1) j / μ j else 0) := by
      intro j; rw [bvec_succ]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
    rfl

lemma K_le {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (hμpos : ∀ j, 0 < μ j)
    (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  have hlt : (K : ℝ) * Real.sqrt m < ∑ i ∈ Finset.range K, scaledSum μ (J1 μ u i) (u (i + 1)) := by
    have : ∑ _i ∈ Finset.range K, Real.sqrt m < ∑ i ∈ Finset.range K, scaledSum μ (J1 μ u i) (u (i + 1)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, Finset.mem_range.mpr hK⟩
      · intro i hi
        obtain ⟨⟨b, hbU, hb⟩, _, hmax⟩ := hrun.1 i (Finset.mem_range.mp hi)
        exact lt_of_lt_of_le hb (hmax b hbU)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  rw [sum_identity] at hlt
  have hle : ∑ j, bvec μ u K j / μ j ≤ ∑ _j : Fin m, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [div_le_iff₀ (hμpos j)]
    exact (inv_bound U μ hμpos hbμ K u hrun K le_rfl j).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hlt2 : (K : ℝ) * Real.sqrt m < (m : ℝ) * 2 := lt_of_lt_of_le hlt hle
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at hlt2
  · have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have hss : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt (by positivity)
    nlinarith

lemma hull_serve {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U G : Set (Fin m → ℝ)) (x : Fin n₁ → ℝ)
    (y : (Fin m → ℝ) → Fin n₂ → ℝ) (hxy : AffinePolicies.Simplex.Feasible A B U x y)
    (α T : ℝ) (hα : 0 ≤ α)
    (hG : ∀ g ∈ G, ∃ w ∈ U, g ≤ α • w ∧ α * (c ⬝ᵥ x + d ⬝ᵥ y w) ≤ T) :
    ∀ v ∈ convexHull ℝ G, ∃ y' : Fin n₂ → ℝ, 0 ≤ y' ∧ v ≤ A *ᵥ (α • x) + B *ᵥ y' ∧
      c ⬝ᵥ (α • x) + d ⬝ᵥ y' ≤ T := by
  have hS : Convex ℝ {v : Fin m → ℝ | ∃ y' : Fin n₂ → ℝ, 0 ≤ y' ∧
      v ≤ A *ᵥ (α • x) + B *ᵥ y' ∧ c ⬝ᵥ (α • x) + d ⬝ᵥ y' ≤ T} := by
    intro v1 hv1 v2 hv2 a b ha hb hab
    obtain ⟨y1, h1, h1', h1''⟩ := hv1
    obtain ⟨y2, h2, h2', h2''⟩ := hv2
    obtain rfl : b = 1 - a := by linarith
    refine ⟨a • y1 + (1 - a) • y2, ?_, ?_, ?_⟩
    · exact add_nonneg (smul_nonneg ha h1) (smul_nonneg hb h2)
    · intro i
      have e1 := h1' i
      have e2 := h2' i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add,
        Matrix.mulVec_smul] at e1 e2 ⊢
      nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]
    · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1'' h2'' ⊢
      nlinarith [mul_le_mul_of_nonneg_left h1'' ha, mul_le_mul_of_nonneg_left h2'' hb]
  have hsub : G ⊆ {v : Fin m → ℝ | ∃ y' : Fin n₂ → ℝ, 0 ≤ y' ∧
      v ≤ A *ᵥ (α • x) + B *ᵥ y' ∧ c ⬝ᵥ (α • x) + d ⬝ᵥ y' ≤ T} := by
    intro g hg
    obtain ⟨w, hwU, hgw, hcost⟩ := hG g hg
    obtain ⟨hy0, hyb⟩ := hxy.2 w hwU
    refine ⟨α • y w, smul_nonneg hα hy0, ?_, ?_⟩
    · refine le_trans hgw ?_
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add]
      exact smul_le_smul_of_nonneg_left hyb hα
    · rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      linarith
  intro v hv
  exact convexHull_min hsub hS hv

lemma dom {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b) (μ : Fin m → ℝ)
    (hμpos : ∀ j, 0 < μ j) (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (β : Fin m → ℝ) (hβ0 : 0 ≤ β) (J : Finset (Fin m)) (hJ : ∀ j ∉ J, μ j ≤ β j)
    (hloop : ∀ b ∈ U, scaledSum μ J b ≤ Real.sqrt m) (hm : 0 < m) :
    ∀ b ∈ U, ∃ b' ∈ convexHull ℝ (Set.range (fun j => (2 * Real.sqrt m) • bstar j) ∪
      {(2 : ℝ) • β}), b ≤ b' := by
  intro b hb
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  set s := Real.sqrt m with hsdef
  have hb0 : 0 ≤ b := hUnn b hb
  set lam : Fin m → ℝ := fun j => if j ∈ J then b j / (μ j * (2 * s)) else 0 with hlam
  have hlam0 : ∀ j, 0 ≤ lam j := by
    intro j; simp only [hlam]; split_ifs
    · exact div_nonneg (hb0 j) (mul_pos (hμpos j) (by linarith)).le
    · exact le_rfl
  have hsum : ∑ j, lam j = scaledSum μ J b / (2 * s) := by
    simp only [hlam, Finset.sum_ite_mem, Finset.univ_inter, scaledSum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [div_div]
  have hsum_le : ∑ j, lam j ≤ 1 / 2 := by
    rw [hsum, div_le_iff₀ (by positivity)]
    have := hloop b hb
    linarith
  set l0 : ℝ := 1 - ∑ j, lam j with hl0
  have hl0' : 1 / 2 ≤ l0 := by linarith
  set G := Set.range (fun j => (2 * s) • bstar j) ∪ {(2 : ℝ) • β} with hG
  set wt : Option (Fin m) → ℝ := fun o => o.elim l0 lam with hwt
  set z : Option (Fin m) → Fin m → ℝ := fun o => o.elim ((2 : ℝ) • β) (fun j => (2 * s) • bstar j)
    with hz
  have hmem : ∑ o, wt o • z o ∈ convexHull ℝ G := by
    apply (convex_convexHull ℝ G).sum_mem
    · intro o _
      cases o with
      | none => simp only [hwt, Option.elim]; linarith
      | some j => exact hlam0 j
    · rw [Fintype.sum_option]
      simp only [hwt, Option.elim, hl0]
      ring
    · intro o _
      apply subset_convexHull
      cases o with
      | none => exact Or.inr rfl
      | some j => exact Or.inl ⟨j, rfl⟩
  refine ⟨_, hmem, ?_⟩
  rw [Fintype.sum_option]
  simp only [hwt, hz, Option.elim]
  intro i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ j ∈ Finset.univ, 0 ≤ lam j * (2 * s * bstar j i) := by
    intro j _
    have h0 : (0 : ℝ) ≤ bstar j i := hUnn _ (hbstar j).1 i
    exact mul_nonneg (hlam0 j) (mul_nonneg (by linarith) h0)
  have hS0 : 0 ≤ ∑ j, lam j * (2 * s * bstar j i) := Finset.sum_nonneg hterm
  have hβi : 0 ≤ β i := hβ0 i
  by_cases hi : i ∈ J
  · have h1 : lam i * (2 * s * bstar i i) ≤ ∑ j, lam j * (2 * s * bstar j i) :=
      Finset.single_le_sum hterm (Finset.mem_univ i)
    have h2 : lam i * (2 * s * bstar i i) = b i := by
      simp only [hlam, if_pos hi, (hbstar i).2]
      have := hμpos i
      field_simp
    have h3 : 0 ≤ l0 * (2 * β i) := by nlinarith
    linarith
  · have h1 : b i ≤ μ i := hbμ b hb i
    have h2 : μ i ≤ β i := hJ i hi
    nlinarith

end P5a698ddd

open Matrix in
theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUconv : Convex ℝ U) (hUcpt : IsCompact U) (hUfull : (interior U).Nonempty)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), AffinePolicies.Simplex.Feasible A B U x y)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u)
    (xt : Fin n₁ → ℝ) (yt : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hopt : AffinePolicies.Simplex.IsOptimalAdapt A B c d (AffinePolicies.GeneralApprox.U0 bstar u K) xt yt) :
    ∀ b ∈ U, ∃ y : Fin n₂ → ℝ, 0 ≤ y ∧ b ≤ A *ᵥ xt + B *ᵥ y ∧
      c ⬝ᵥ xt + d ⬝ᵥ y ≤ 4 * Real.sqrt m * AffinePolicies.Simplex.zAdapt A B c d U := by
  classical
  have hμpos : ∀ j, 0 < μ j := P5a698ddd.mu_pos' U hUnn hUfull μ hμ
  have hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j := fun b hb j => (hμ j).2 ⟨b, hb, rfl⟩
  set α : ℝ := 4 * Real.sqrt m with hαdef
  have hsq : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hα : 0 ≤ α := by positivity
  have hK : (K : ℝ) ≤ 2 * Real.sqrt m := P5a698ddd.K_le U μ hμpos hbμ K u hrun
  set β := AffinePolicies.SqrtBound.betaSum u K with hβdef
  have hβsum : ∀ j, β j = ∑ i ∈ Finset.Icc 1 K, u i j := by
    intro j; simp [hβdef, AffinePolicies.SqrtBound.betaSum, Finset.sum_apply]
  have humem : ∀ i ∈ Finset.Icc 1 K, u i ∈ U := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact P5a698ddd.u_mem U μ K u hrun k (by omega)
  have hβ0 : 0 ≤ β := by
    intro j; rw [hβsum]
    exact Finset.sum_nonneg (fun i hi => hUnn _ (humem i hi) j)
  -- a point of U
  obtain ⟨p, hp⟩ := hUfull
  have hpU : p ∈ U := interior_subset hp
  -- witness for 2β
  obtain ⟨w0, hw0U, hw0⟩ : ∃ w0 ∈ U, (2 : ℝ) • β ≤ α • w0 := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · refine ⟨p, hpU, ?_⟩
      have : β = 0 := by
        funext j; rw [hβsum]; subst hK0; simp
      rw [this, smul_zero]
      exact smul_nonneg hα (hUnn p hpU)
    · have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
      refine ⟨(K : ℝ)⁻¹ • β, ?_, ?_⟩
      · have : (K : ℝ)⁻¹ • β = ∑ i ∈ Finset.Icc 1 K, (K : ℝ)⁻¹ • u i := by
          rw [← Finset.smul_sum]; rfl
        rw [this]
        apply hUconv.sum_mem
        · intro i _; positivity
        · simp [Finset.sum_const, Nat.card_Icc]; field_simp
        · exact humem
      · intro j
        simp only [Pi.smul_apply, smul_eq_mul]
        have hj : (0 : ℝ) ≤ β j := hβ0 j
        rw [← mul_assoc]
        have : 2 ≤ α * (K : ℝ)⁻¹ := by
          rw [hαdef, le_mul_inv_iff₀ hKpos]; linarith
        exact mul_le_mul_of_nonneg_right this hj
  -- generators
  have hgen : ∀ g ∈ Set.range (fun j => (2 * Real.sqrt m) • bstar j) ∪ {(2 : ℝ) • β},
      g ≤ α • w0 ∨ ∃ j, g ≤ α • bstar j := by
    rintro g (⟨j, rfl⟩ | hg)
    · right; refine ⟨j, fun i => ?_⟩
      have h0 : (0 : ℝ) ≤ bstar j i := hUnn _ (hbstar j).1 i
      simp only [Pi.smul_apply, smul_eq_mul, hαdef]
      nlinarith
    · left; rw [Set.mem_singleton_iff.mp hg]; exact hw0
  have hU0 : AffinePolicies.GeneralApprox.U0 bstar u K =
      convexHull ℝ (Set.range (fun j => (2 * Real.sqrt m) • bstar j) ∪ {(2 : ℝ) • β}) := rfl
  -- serving U0 from any feasible solution on U with a bound at the generators
  have serve : ∀ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (T : ℝ),
      AffinePolicies.Simplex.Feasible A B U x y →
      α * (c ⬝ᵥ x + d ⬝ᵥ y w0) ≤ T → (∀ j, α * (c ⬝ᵥ x + d ⬝ᵥ y (bstar j)) ≤ T) →
      T ∈ {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
        AffinePolicies.Simplex.Feasible A B (AffinePolicies.GeneralApprox.U0 bstar u K) x y ∧
        AffinePolicies.Simplex.CostLE c d (AffinePolicies.GeneralApprox.U0 bstar u K) x y t} := by
    intro x y T hxy hT0 hTj
    have h := P5a698ddd.hull_serve A B c d U _ x y hxy α T hα (by
      intro g hg
      rcases hgen g hg with h | ⟨j, h⟩
      · exact ⟨w0, hw0U, h, hT0⟩
      · exact ⟨bstar j, (hbstar j).1, h, hTj j⟩)
    rw [← hU0] at h
    choose! y' hy' using h
    refine ⟨α • x, y', ⟨smul_nonneg hα hxy.1, fun v hv => ⟨(hy' v hv).1, (hy' v hv).2.1⟩⟩,
      fun v hv => (hy' v hv).2.2⟩
  -- nonnegativity of costs on U0
  have h2βmem : (2 : ℝ) • β ∈ AffinePolicies.GeneralApprox.U0 bstar u K := by
    rw [hU0]; exact subset_convexHull _ _ (Or.inr rfl)
  have hbdd : BddBelow {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
      AffinePolicies.Simplex.Feasible A B (AffinePolicies.GeneralApprox.U0 bstar u K) x y ∧
      AffinePolicies.Simplex.CostLE c d (AffinePolicies.GeneralApprox.U0 bstar u K) x y t} := by
    refine ⟨0, ?_⟩
    rintro t ⟨x, y, hxy, hcost⟩
    have := hcost _ h2βmem
    have h1 := dotProduct_nonneg_of_nonneg hc hxy.1
    have h2 := dotProduct_nonneg_of_nonneg hd (hxy.2 _ h2βmem).1
    linarith
  -- a finite-cost solution on U0
  obtain ⟨x0, y0, hxy0⟩ := hfeas
  set f : (Fin m → ℝ) → ℝ := fun w => |α * (c ⬝ᵥ x0 + d ⬝ᵥ y0 w)| with hf
  set T0 : ℝ := f w0 + ∑ j, f (bstar j) with hT0
  have hT0mem := serve x0 y0 T0 hxy0
    (by
      have : 0 ≤ ∑ j, f (bstar j) := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      have := le_abs_self (α * (c ⬝ᵥ x0 + d ⬝ᵥ y0 w0))
      simp only [hT0, hf] at *; linarith)
    (by
      intro j
      have h1 : f (bstar j) ≤ ∑ j, f (bstar j) :=
        Finset.single_le_sum (f := fun j => f (bstar j)) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 := le_abs_self (α * (c ⬝ᵥ x0 + d ⬝ᵥ y0 (bstar j)))
      have h3 : 0 ≤ f w0 := abs_nonneg _
      simp only [hT0, hf] at *; linarith)
  -- dominance
  have hdom : ∀ b ∈ U, ∃ b' ∈ AffinePolicies.GeneralApprox.U0 bstar u K, b ≤ b' := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · intro b _
      exact ⟨_, h2βmem, fun i => (Fin.cast hm i).elim0⟩
    · rw [hU0]
      apply P5a698ddd.dom U hUnn μ hμpos hbμ bstar hbstar β hβ0 (AffinePolicies.SqrtBound.J1 μ u K)
      · intro j hj
        have h1 := P5a698ddd.ge_mu μ u K j hj
        have h2 := P5a698ddd.bvec_le_sum U hUnn μ K u hrun K le_rfl j
        rw [hβsum]; linarith
      · intro b hb
        by_contra hcon
        exact hrun.2 ⟨b, hb, lt_of_not_ge hcon⟩
      · exact hm
  choose! bd hbdU hbd using hdom
  -- the U-set is nonempty
  obtain ⟨x1, y1, hxy1, hc1⟩ := hT0mem
  have hUne : (T0 : ℝ) ∈ {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
      AffinePolicies.Simplex.Feasible A B U x y ∧ AffinePolicies.Simplex.CostLE c d U x y t} := by
    refine ⟨x1, fun b => y1 (bd b), ⟨hxy1.1, fun b hb => ⟨(hxy1.2 _ (hbdU b hb)).1,
      le_trans (hbd b hb) (hxy1.2 _ (hbdU b hb)).2⟩⟩, fun b hb => hc1 _ (hbdU b hb)⟩
  -- zAdapt U0 ≤ α * zAdapt U
  have hz : AffinePolicies.Simplex.zAdapt A B c d (AffinePolicies.GeneralApprox.U0 bstar u K) ≤
      α * AffinePolicies.Simplex.zAdapt A B c d U := by
    have key : ∀ t ∈ {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
        AffinePolicies.Simplex.Feasible A B U x y ∧ AffinePolicies.Simplex.CostLE c d U x y t},
        AffinePolicies.Simplex.zAdapt A B c d (AffinePolicies.GeneralApprox.U0 bstar u K) ≤ α * t := by
      rintro t ⟨x, y, hxy, hcost⟩
      apply csInf_le hbdd
      exact serve x y (α * t) hxy
        (mul_le_mul_of_nonneg_left (hcost w0 hw0U) hα)
        (fun j => mul_le_mul_of_nonneg_left (hcost _ (hbstar j).1) hα)
    rcases eq_or_lt_of_le hα with h0 | hpos
    · have := key _ hUne
      rw [← h0] at this ⊢; simpa using this
    · have : AffinePolicies.Simplex.zAdapt A B c d (AffinePolicies.GeneralApprox.U0 bstar u K) / α ≤
          AffinePolicies.Simplex.zAdapt A B c d U := by
        apply le_csInf ⟨_, hUne⟩
        intro t ht
        rw [div_le_iff₀ hpos, mul_comm]
        exact key t ht
      rwa [div_le_iff₀ hpos, mul_comm] at this
  -- final
  intro b hb
  obtain ⟨hfeast, hbest⟩ := hopt
  refine ⟨yt (bd b), (hfeast.2 _ (hbdU b hb)).1, le_trans (hbd b hb) (hfeast.2 _ (hbdU b hb)).2, ?_⟩
  refine le_trans ?_ hz
  unfold AffinePolicies.Simplex.zAdapt
  refine le_csInf ⟨T0, x1, y1, hxy1, hc1⟩ ?_
  rintro t ⟨x', y', hf', hc'⟩
  exact hbest x' y' t hf' hc' _ (hbdU b hb)
