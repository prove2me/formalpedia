-- Prove2me | solution 1 for AffinePolicies.SqrtBound.constructed_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:41:31.490337+00:00
-- url     : https://prove2.me/submissions/94d1f3bb-8070-4bee-af75-3ebd2c3486c8

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix


namespace AffinePolicies.SqrtBound

theorem g34_bvec_succ {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) (j : Fin m) :
    bvec μ u (k + 1) j = if j ∈ J1 μ u k then bvec μ u k j + u (k + 1) j else bvec μ u k j := by
  simp only [bvec, J1, algState]
  by_cases h : j ∈ (algState μ u k).2 <;> simp [h]

theorem g34_J1_succ {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) :
    J1 μ u (k + 1) = (J1 μ u k).filter (fun j => bvec μ u (k + 1) j < μ j) := by
  ext j
  simp only [J1, bvec, algState]

theorem g34_bvec_zero {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) : bvec μ u 0 = 0 := by
  simp [bvec, algState]

theorem g34_J1_zero {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) : J1 μ u 0 = Finset.univ := by
  simp [J1, algState]

theorem g34_bvec_eq_sum {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) (j : Fin m) :
    bvec μ u K j = ∑ k ∈ Finset.range K, if j ∈ J1 μ u k then u (k + 1) j else 0 := by
  induction K with
  | zero => simp [g34_bvec_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, g34_bvec_succ]
    split_ifs <;> simp

theorem g34_notmem_ge {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) :
    ∀ j, j ∉ J1 μ u K → μ j ≤ bvec μ u K j := by
  induction K with
  | zero => intro j hj; simp [g34_J1_zero] at hj
  | succ K ih =>
    intro j hj
    rw [g34_J1_succ, Finset.mem_filter] at hj
    by_cases h : j ∈ J1 μ u K
    · push Not at hj
      exact hj h
    · rw [g34_bvec_succ, if_neg h]
      exact ih j h

theorem g34_mem_lt {m : ℕ} (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (hμpos : ∀ j, 0 < μ j) (k : ℕ)
    (j : Fin m) (hj : j ∈ J1 μ u k) : bvec μ u k j < μ j := by
  cases k with
  | zero => simp [g34_bvec_zero, hμpos j]
  | succ k =>
    rw [g34_J1_succ, Finset.mem_filter] at hj
    exact hj.2

theorem g34_betaSum_eq {m : ℕ} (u : ℕ → Fin m → ℝ) (K : ℕ) (j : Fin m) :
    betaSum u K j = ∑ k ∈ Finset.range K, u (k + 1) j := by
  unfold betaSum
  rw [Finset.sum_apply]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem g34_lemma9 {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    (∀ b ∈ U, scaledSum μ (J1 μ u K) b ≤ Real.sqrt m) ∧
      ∀ j, j ∉ J1 μ u K → ∀ b ∈ U, b j ≤ betaSum u K j := by
  obtain ⟨hit, hnot⟩ := hrun
  refine ⟨?_, ?_⟩
  · intro b hb
    by_contra h
    exact hnot ⟨b, hb, lt_of_not_ge h⟩
  · intro j hj b hb
    have h1 : b j ≤ μ j := (hμ j).2 ⟨b, hb, rfl⟩
    have h2 := g34_notmem_ge μ u K j hj
    have h3 : bvec μ u K j ≤ betaSum u K j := by
      rw [g34_bvec_eq_sum, g34_betaSum_eq]
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k < K := Finset.mem_range.mp hk
      have hu : 0 ≤ u (k + 1) j := hUnn _ (hit k hk').2.1 j
      split_ifs <;> linarith
    linarith

theorem g34_lemma10 {m : ℕ} (U : Set (Fin m → ℝ))
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  -- sum of scaled sums
  have hsum : ∑ k ∈ Finset.range K, scaledSum μ (J1 μ u k) (u (k + 1)) =
      ∑ j, bvec μ u K j / μ j := by
    have : ∀ k, scaledSum μ (J1 μ u k) (u (k + 1)) =
        ∑ j, (if j ∈ J1 μ u k then u (k + 1) j else 0) / μ j := by
      intro k
      unfold scaledSum
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ J1 μ u k)]
      have e1 : Finset.univ.filter (fun j => j ∈ J1 μ u k) = J1 μ u k := by
        ext; simp
      rw [e1]
      have e2 : ∑ x ∈ Finset.univ.filter (fun j => j ∉ J1 μ u k),
          (if x ∈ J1 μ u k then u (k + 1) x else 0) / μ x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_filter] at hx
        simp [hx.2]
      rw [e2, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx]
    simp_rw [this]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [g34_bvec_eq_sum, Finset.sum_div]
  -- each iteration contributes > √m
  have hlow : (K : ℝ) * Real.sqrt m < ∑ k ∈ Finset.range K, scaledSum μ (J1 μ u k) (u (k + 1)) := by
    have : ∑ k ∈ Finset.range K, Real.sqrt m <
        ∑ k ∈ Finset.range K, scaledSum μ (J1 μ u k) (u (k + 1)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, Finset.mem_range.mpr hK⟩
      · intro k hk
        obtain ⟨⟨b, hb, hlt⟩, _, hmax⟩ := hiter k (Finset.mem_range.mp hk)
        exact lt_of_lt_of_le hlt (hmax b hb)
    simpa using this
  -- bvec bounded by 2μ
  have hbv : ∀ j, ∀ k ≤ K, bvec μ u k j < 2 * μ j := by
    intro j k
    induction k with
    | zero => intro _; simp [g34_bvec_zero]; linarith [hμpos j]
    | succ k ih =>
      intro hk
      rw [g34_bvec_succ]
      split_ifs with h
      · have h1 := g34_mem_lt μ u hμpos k j h
        have h2 : u (k + 1) j ≤ μ j := (hμ j).2 ⟨u (k + 1), (hiter k (by omega)).2.1, rfl⟩
        linarith
      · exact ih (by omega)
  have hup : ∑ j, bvec μ u K j / μ j ≤ ∑ _j : Fin m, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [div_le_iff₀ (hμpos j)]
    linarith [hbv j K le_rfl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hup
  have hm : (m : ℝ) = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt (Nat.cast_nonneg m)).symm
  rw [hsum] at hlow
  have hk2 : (K : ℝ) * Real.sqrt m < 2 * (Real.sqrt m * Real.sqrt m) := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith


theorem g34_Pb {m n₂ : ℕ} (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (bstar : Fin m → Fin m → ℝ)
    (μ : Fin m → ℝ) (J : Finset (Fin m)) (b : Fin m → ℝ) :
    thmPolicyP ys bstar μ J *ᵥ b = ∑ j ∈ J, (b j / μ j) • ys (bstar j) := by
  funext i
  simp only [mulVec, dotProduct, thmPolicyP, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  have : ∀ j, (if j ∈ J then ys (bstar j) i / μ j else 0) * b j =
      if j ∈ J then b j / μ j * ys (bstar j) i else 0 := by
    intro j; split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem g34_card_Icc (K : ℕ) : ((Finset.Icc 1 K).card : ℝ) = K := by
  simp

theorem g34_uK {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (K : ℕ) (u : ℕ → Fin m → ℝ)
    (hrun : IsRun U μ K u) : ∀ k ∈ Finset.Icc 1 K, u k ∈ U := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact (hrun.1 k' (by omega)).2.1

theorem g34_cK {m : ℕ} (K : ℕ) : 2 * Real.sqrt m / K * K ≤ 2 * Real.sqrt m := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · rw [div_mul_cancel₀]; exact_mod_cast hK.ne'

theorem g34_feasible {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (U : Set (Fin m → ℝ))
    (hA : ∀ i j, 0 ≤ A i j) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    AffinePolicies.Simplex.Feasible A B U ((3 * Real.sqrt m) • xs)
      (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K)) := by
  obtain ⟨hx0, hy⟩ := hfs
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have h9 := g34_lemma9 U hUnn μ hμ K u hrun
  have h10 := g34_lemma10 U μ hμ hμpos K u hrun.1
  have huK := g34_uK U μ K u hrun
  set J := J1 μ u K with hJ
  set c : ℝ := 2 * Real.sqrt m / K with hc
  have hc0 : 0 ≤ c := by positivity
  have hcK : c * K ≤ 2 * Real.sqrt m := g34_cK K
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonneg (by positivity) (hx0 i)
  intro b hb
  have hb0 := hUnn b hb
  have hy' : AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ J) (thmPolicyq ys u K) b =
      ∑ j ∈ J, (b j / μ j) • ys (bstar j) + c • ∑ k ∈ Finset.Icc 1 K, ys (u k) := by
    simp only [AffinePolicies.Simplex.affinePolicy, g34_Pb, thmPolicyq, hc]
  rw [hy']
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply add_nonneg
    · apply Finset.sum_nonneg; intro j _
      exact mul_nonneg (div_nonneg (hb0 j) (hμpos j).le) ((hy _ (hbstar j).1).1 i)
    · apply mul_nonneg hc0
      apply Finset.sum_nonneg; intro k hk
      exact (hy _ (huK k hk)).1 i
  intro i
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_sum]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_smul]
  set a := (A *ᵥ xs) i with ha
  have ha0 : 0 ≤ a := by
    simp only [ha, mulVec, dotProduct]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (hx0 j))
  have hfb : ∀ b' ∈ U, b' i - a ≤ (B *ᵥ ys b') i := by
    intro b' hb'
    have := (hy b' hb').2 i
    simp only [Pi.add_apply] at this
    linarith
  have hX : ∑ j ∈ J, b j / μ j * (bstar j i - a) ≤ ∑ j ∈ J, b j / μ j * (B *ᵥ ys (bstar j)) i := by
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_left (hfb _ (hbstar j).1) (div_nonneg (hb0 j) (hμpos j).le)
  have hY : ∑ k ∈ Finset.Icc 1 K, (u k i - a) ≤ ∑ k ∈ Finset.Icc 1 K, (B *ᵥ ys (u k)) i := by
    apply Finset.sum_le_sum; intro k hk
    exact hfb _ (huK k hk)
  have hX' : ∑ j ∈ J, b j / μ j * (bstar j i - a) =
      ∑ j ∈ J, b j / μ j * bstar j i - scaledSum μ J b * a := by
    unfold scaledSum
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hY' : ∑ k ∈ Finset.Icc 1 K, (u k i - a) = ∑ k ∈ Finset.Icc 1 K, u k i - K * a := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, g34_card_Icc]
  have hS : scaledSum μ J b ≤ Real.sqrt m := h9.1 b hb
  have hT1 : 0 ≤ ∑ j ∈ J, b j / μ j * bstar j i := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (div_nonneg (hb0 j) (hμpos j).le) (hUnn _ (hbstar j).1 i))
  have hT2 : 0 ≤ ∑ k ∈ Finset.Icc 1 K, u k i :=
    Finset.sum_nonneg (fun k hk => hUnn _ (huK k hk) i)
  have key : b i ≤ ∑ j ∈ J, b j / μ j * bstar j i + c * ∑ k ∈ Finset.Icc 1 K, u k i := by
    by_cases hiJ : i ∈ J
    · have := Finset.single_le_sum (f := fun j => b j / μ j * bstar j i)
        (fun j _ => mul_nonneg (div_nonneg (hb0 j) (hμpos j).le) (hUnn _ (hbstar j).1 i)) hiJ
      simp only [(hbstar i).2] at this
      rw [div_mul_cancel₀ _ (hμpos i).ne'] at this
      nlinarith
    · have hK : 0 < K := by
        rcases Nat.eq_zero_or_pos K with h | h
        · exfalso; apply hiJ; rw [hJ, h, g34_J1_zero]; exact Finset.mem_univ _
        · exact h
      have hc1 : 1 ≤ c := by
        rw [hc, le_div_iff₀ (by exact_mod_cast hK)]; linarith
      have hbeta := h9.2 i hiJ b hb
      rw [g34_betaSum_eq, ← Finset.sum_apply] at hbeta
      have e : ∑ k ∈ Finset.Icc 1 K, u k i = ∑ k ∈ Finset.range K, u (k + 1) i := by
        have := g34_betaSum_eq u K i
        unfold betaSum at this
        rw [Finset.sum_apply] at this
        exact this
      rw [Finset.sum_apply] at hbeta
      rw [e] at hT2 ⊢
      nlinarith
  have hsa : scaledSum μ J b * a ≤ Real.sqrt m * a := mul_le_mul_of_nonneg_right hS ha0
  have hca : c * (K * a) ≤ 2 * Real.sqrt m * a := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcK ha0
  have hcY := mul_le_mul_of_nonneg_left hY hc0
  rw [hY'] at hcY
  rw [hX'] at hX
  nlinarith

theorem g34_cost {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    ∀ t : ℝ, AffinePolicies.Simplex.CostLE c d U xs ys t →
      AffinePolicies.Simplex.CostLE c d U ((3 * Real.sqrt m) • xs)
        (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K))
        (3 * Real.sqrt m * t) := by
  intro t ht b hb
  obtain ⟨_, hy⟩ := hfs
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have h9 := g34_lemma9 U hUnn μ hμ K u hrun
  have huK := g34_uK U μ K u hrun
  set J := J1 μ u K with hJ
  set γ : ℝ := 2 * Real.sqrt m / K with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hγK : γ * K ≤ 2 * Real.sqrt m := g34_cK K
  have hb0 := hUnn b hb
  have hy' : AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ J) (thmPolicyq ys u K) b =
      ∑ j ∈ J, (b j / μ j) • ys (bstar j) + γ • ∑ k ∈ Finset.Icc 1 K, ys (u k) := by
    simp only [AffinePolicies.Simplex.affinePolicy, g34_Pb, thmPolicyq, hγ]
  rw [hy']
  rw [dotProduct_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, dotProduct_sum]
  simp only [smul_eq_mul, dotProduct_smul]
  set e := t - c ⬝ᵥ xs with he
  have hde : ∀ b' ∈ U, d ⬝ᵥ ys b' ≤ e := by
    intro b' hb'; have := ht b' hb'; rw [he]; linarith
  have hdn : ∀ b' ∈ U, 0 ≤ d ⬝ᵥ ys b' := by
    intro b' hb'
    simp only [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hd i) ((hy b' hb').1 i))
  have he0 : 0 ≤ e := le_trans (hdn b hb) (hde b hb)
  have hX : ∑ j ∈ J, b j / μ j * (d ⬝ᵥ ys (bstar j)) ≤ scaledSum μ J b * e := by
    unfold scaledSum; rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_left (hde _ (hbstar j).1) (div_nonneg (hb0 j) (hμpos j).le)
  have hY : ∑ k ∈ Finset.Icc 1 K, d ⬝ᵥ ys (u k) ≤ K * e := by
    have : ∑ k ∈ Finset.Icc 1 K, d ⬝ᵥ ys (u k) ≤ ∑ k ∈ Finset.Icc 1 K, e :=
      Finset.sum_le_sum (fun k hk => hde _ (huK k hk))
    rw [Finset.sum_const, nsmul_eq_mul, g34_card_Icc] at this
    exact this
  have hS : scaledSum μ J b ≤ Real.sqrt m := h9.1 b hb
  have h1 : scaledSum μ J b * e ≤ Real.sqrt m * e := mul_le_mul_of_nonneg_right hS he0
  have h2 : γ * ∑ k ∈ Finset.Icc 1 K, d ⬝ᵥ ys (u k) ≤ γ * (K * e) :=
    mul_le_mul_of_nonneg_left hY hγ0
  have h3 : γ * (K * e) ≤ 2 * Real.sqrt m * e := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hγK he0
  have : t = c ⬝ᵥ xs + e := by rw [he]; ring
  rw [this]
  nlinarith

end AffinePolicies.SqrtBound

open AffinePolicies.SqrtBound


theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (U : Set (Fin m → ℝ))
    (hA : ∀ i j, 0 ≤ A i j) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    AffinePolicies.Simplex.Feasible A B U ((3 * Real.sqrt m) • xs)
      (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K)) := by
  exact g34_feasible A B U hA hUnn μ hμ hμpos bstar hbstar K u hrun xs ys hfs
