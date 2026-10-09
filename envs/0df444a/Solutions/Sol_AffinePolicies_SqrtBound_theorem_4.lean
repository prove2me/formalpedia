-- Prove2me | solution 1 for AffinePolicies.SqrtBound.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:01:58.342894+00:00
-- url     : https://prove2.me/submissions/e3b8ea68-ff3f-41a6-9387-821a6c4ad35e

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

set_option autoImplicit false

namespace P8c660a2b

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
    (hiter : ∀ k < K, IsIteration U μ u k) (k : ℕ) (hk : k < K) : u (k + 1) ∈ U :=
  (hiter k hk).2.1

lemma bvec_le_sum {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b) (μ : Fin m → ℝ)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    ∀ k ≤ K, ∀ j, bvec μ u k j ≤ ∑ i ∈ Finset.Icc 1 k, u i j := by
  intro k
  induction k with
  | zero => intro _ j; simp [bvec_zero]
  | succ k ih =>
    intro hk j
    have h0 : 0 ≤ u (k + 1) j := hUnn _ (u_mem U μ K u hiter k (by omega)) j
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
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
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
    have hu : u (k + 1) j ≤ μ j := hbμ _ (u_mem U μ K u hiter k (by omega)) j
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
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter]
    rfl

lemma K_le {m : ℕ} (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (hμpos : ∀ j, 0 < μ j)
    (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  have hlt : (K : ℝ) * Real.sqrt m <
      ∑ i ∈ Finset.range K, scaledSum μ (J1 μ u i) (u (i + 1)) := by
    have : ∑ _i ∈ Finset.range K, Real.sqrt m <
        ∑ i ∈ Finset.range K, scaledSum μ (J1 μ u i) (u (i + 1)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, Finset.mem_range.mpr hK⟩
      · intro i hi
        obtain ⟨⟨b, hbU, hb⟩, _, hmax⟩ := hiter i (Finset.mem_range.mp hi)
        exact lt_of_lt_of_le hb (hmax b hbU)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  rw [sum_identity] at hlt
  have hle : ∑ j, bvec μ u K j / μ j ≤ ∑ _j : Fin m, (2 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [div_le_iff₀ (hμpos j)]
    exact (inv_bound U μ hμpos hbμ K u hiter K le_rfl j).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hlt2 : (K : ℝ) * Real.sqrt m < (m : ℝ) * 2 := lt_of_lt_of_le hlt hle
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at hlt2
  · have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have hss : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt (by positivity)
    nlinarith

/-- Algorithm 𝒜 terminates: it has a complete run. -/
lemma exists_run {m : ℕ} (U : Set (Fin m → ℝ)) (hUcpt : IsCompact U) (hUne : U.Nonempty)
    (μ : Fin m → ℝ) (hμpos : ∀ j, 0 < μ j) (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j) :
    ∃ (K : ℕ) (u : ℕ → Fin m → ℝ), IsRun U μ K u := by
  have hg : ∀ J : Finset (Fin m), ∃ g ∈ U, ∀ b ∈ U, scaledSum μ J b ≤ scaledSum μ J g := by
    intro J
    have hc : Continuous (fun b : Fin m → ℝ => scaledSum μ J b) := by
      unfold scaledSum
      exact continuous_finsetSum _ (fun j _ => (continuous_apply j).div_const _)
    obtain ⟨g, hgU, hmax⟩ := hUcpt.exists_isMaxOn hUne hc.continuousOn
    exact ⟨g, hgU, fun b hb => hmax hb⟩
  choose g hgU hgmax using hg
  let st : ℕ → (Fin m → ℝ) × Finset (Fin m) := fun n =>
    Nat.rec ((0 : Fin m → ℝ), (Finset.univ : Finset (Fin m)))
      (fun _ s =>
        ((fun j => if j ∈ s.2 then s.1 j + g s.2 j else s.1 j),
          s.2.filter (fun j => (if j ∈ s.2 then s.1 j + g s.2 j else s.1 j) < μ j))) n
  let u : ℕ → Fin m → ℝ := fun n => Nat.casesOn n 0 (fun k => g (st k).2)
  have hst : ∀ k, algState μ u k = st k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [algState, ih]
  have hJ : ∀ k, J1 μ u k = (st k).2 := fun k => by
    show (algState μ u k).2 = _
    rw [hst]
  have hu : ∀ k, u (k + 1) = g (J1 μ u k) := fun k => by
    rw [hJ k]
  have hiter : ∀ k, LoopCond U μ (J1 μ u k) → IsIteration U μ u k := fun k hk =>
    ⟨hk, by rw [hu]; exact hgU _, by rw [hu]; exact hgmax _⟩
  have hex : ∃ k, ¬ LoopCond U μ (J1 μ u k) := by
    by_contra hcon
    have h1 := K_le U μ hμpos hbμ (⌈2 * Real.sqrt m⌉₊ + 1) u
      (fun k _ => hiter k (not_not.mp (not_exists.mp hcon k)))
    have h2 : 2 * Real.sqrt m ≤ (⌈2 * Real.sqrt m⌉₊ : ℝ) := Nat.le_ceil _
    push_cast at h1
    linarith
  classical
  refine ⟨Nat.find hex, u, fun k hk => hiter k ?_, Nat.find_spec hex⟩
  exact not_not.mp (Nat.find_min hex hk)

lemma P_mulVec {m n₂ : ℕ} (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (bstar : Fin m → Fin m → ℝ)
    (μ : Fin m → ℝ) (J : Finset (Fin m)) (b : Fin m → ℝ) :
    thmPolicyP ys bstar μ J *ᵥ b = ∑ l ∈ J, (b l / μ l) • ys (bstar l) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, thmPolicyP, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl (fun l _ => by ring)

lemma run_facts {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    (∀ k ∈ Finset.Icc 1 K, u k ∈ U) ∧ (∀ b ∈ U, scaledSum μ (J1 μ u K) b ≤ Real.sqrt m) ∧
      (∀ j, j ∉ J1 μ u K → ∀ b ∈ U, b j ≤ ∑ k ∈ Finset.Icc 1 K, u k j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact u_mem U μ K u hrun.1 k (by omega)
  · intro b hb
    exact le_of_not_gt (fun h => hrun.2 ⟨b, hb, h⟩)
  · intro j hj b hb
    have h1 := ge_mu μ u K j hj
    have h2 := bvec_le_sum U hUnn μ K u hrun.1 K le_rfl j
    have h3 := hbμ b hb j
    linarith

lemma feas {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (U : Set (Fin m → ℝ)) (hA : ∀ i j, 0 ≤ A i j) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμpos : ∀ j, 0 < μ j) (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    AffinePolicies.Simplex.Feasible A B U ((3 * Real.sqrt m) • xs)
      (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K))
        (thmPolicyq ys u K)) := by
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hK : (K : ℝ) ≤ 2 * Real.sqrt m := K_le U μ hμpos hbμ K u hrun.1
  obtain ⟨humem, hloop, hJc⟩ := run_facts U hUnn μ hbμ K u hrun
  refine ⟨smul_nonneg (by positivity) hfs.1, fun b hb => ⟨?_, ?_⟩⟩
  · simp only [AffinePolicies.Simplex.affinePolicy, P_mulVec, thmPolicyq]
    apply add_nonneg
    · exact Finset.sum_nonneg (fun l _ => smul_nonneg
        (div_nonneg (hUnn b hb l) (hμpos l).le) (hfs.2 _ (hbstar l).1).1)
    · exact smul_nonneg (by positivity)
        (Finset.sum_nonneg (fun k hk => (hfs.2 _ (humem k hk)).1))
  · intro i
    simp only [AffinePolicies.Simplex.affinePolicy, P_mulVec, thmPolicyq, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    set s := Real.sqrt m with hsdef
    set J := J1 μ u K with hJdef
    set a := (A *ᵥ xs) i with hadef
    have ha : 0 ≤ a := by
      simp only [hadef, Matrix.mulVec, dotProduct]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (hfs.1 j))
    have hF : ∀ v ∈ U, v i - a ≤ (B *ᵥ ys v) i := fun v hv => by
      have := (hfs.2 v hv).2 i
      simp only [Pi.add_apply] at this
      linarith
    have hw : ∀ l, 0 ≤ b l / μ l := fun l => div_nonneg (hUnn b hb l) (hμpos l).le
    have h1 : ∑ l ∈ J, b l / μ l * bstar l i - a * s ≤
        ∑ l ∈ J, b l / μ l * (B *ᵥ ys (bstar l)) i := by
      have e : ∑ l ∈ J, b l / μ l * (bstar l i - a) ≤
          ∑ l ∈ J, b l / μ l * (B *ᵥ ys (bstar l)) i :=
        Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hF _ (hbstar l).1) (hw l))
      have e2 : ∑ l ∈ J, b l / μ l * (bstar l i - a) =
          ∑ l ∈ J, b l / μ l * bstar l i - a * scaledSum μ J b := by
        simp only [scaledSum, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e3 := hloop b hb
      have e4 : a * scaledSum μ J b ≤ a * s := mul_le_mul_of_nonneg_left e3 ha
      linarith
    have hS0 : 0 ≤ ∑ l ∈ J, b l / μ l * bstar l i :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (hw l) (hUnn _ (hbstar l).1 i))
    have hβ0 : 0 ≤ ∑ k ∈ Finset.Icc 1 K, u k i :=
      Finset.sum_nonneg (fun k hk => hUnn _ (humem k hk) i)
    have h2 : ∑ k ∈ Finset.Icc 1 K, u k i - K * a ≤
        ∑ k ∈ Finset.Icc 1 K, (B *ᵥ ys (u k)) i := by
      have := Finset.sum_le_sum (fun k hk => hF (u k) (humem k hk))
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
      simpa using this
    have hQ : 2 * s / K * ∑ k ∈ Finset.Icc 1 K, u k i - 2 * s * a ≤
        2 * s / K * ∑ k ∈ Finset.Icc 1 K, (B *ᵥ ys (u k)) i := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · subst hK0; simp; positivity
      · have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * s / K)
        have e : 2 * s / K * (∑ k ∈ Finset.Icc 1 K, u k i - K * a) =
            2 * s / K * ∑ k ∈ Finset.Icc 1 K, u k i - 2 * s * a := by
          field_simp
        linarith
    by_cases hi : i ∈ J
    · have hbi : b i / μ i * bstar i i ≤ ∑ l ∈ J, b l / μ l * bstar l i :=
        Finset.single_le_sum (f := fun l => b l / μ l * bstar l i)
          (fun l _ => mul_nonneg (hw l) (hUnn _ (hbstar l).1 i)) hi
      have hbi' : b i / μ i * bstar i i = b i := by
        rw [(hbstar i).2]; field_simp [(hμpos i).ne']
      have hq0 : 0 ≤ 2 * s / K * ∑ k ∈ Finset.Icc 1 K, u k i := by positivity
      nlinarith
    · have hKpos : 0 < K := by
        rcases Nat.eq_zero_or_pos K with hK0 | hKpos
        · exfalso; apply hi; rw [hJdef, hK0, J1_zero]; exact Finset.mem_univ i
        · exact hKpos
      have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have hbβ := hJc i hi b hb
      have hge : 1 ≤ 2 * s / K := by rw [le_div_iff₀ hKr]; linarith
      have hq : ∑ k ∈ Finset.Icc 1 K, u k i ≤ 2 * s / K * ∑ k ∈ Finset.Icc 1 K, u k i := by
        nlinarith
      nlinarith

lemma cost {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμpos : ∀ j, 0 < μ j) (hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) (t : ℝ)
    (ht : AffinePolicies.Simplex.CostLE c d U xs ys t) :
    AffinePolicies.Simplex.CostLE c d U ((3 * Real.sqrt m) • xs)
      (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K))
      (3 * Real.sqrt m * t) := by
  intro b hb
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hK : (K : ℝ) ≤ 2 * Real.sqrt m := K_le U μ hμpos hbμ K u hrun.1
  obtain ⟨humem, hloop, -⟩ := run_facts U hUnn μ hbμ K u hrun
  simp only [AffinePolicies.Simplex.affinePolicy, P_mulVec, thmPolicyq, dotProduct_add,
    dotProduct_smul, dotProduct_sum, smul_eq_mul]
  set s := Real.sqrt m with hsdef
  set J := J1 μ u K with hJdef
  set e := t - c ⬝ᵥ xs with hedef
  have hD : ∀ v ∈ U, d ⬝ᵥ ys v ≤ e := fun v hv => by
    have := ht v hv; rw [hedef]; linarith
  have hD0 : ∀ v ∈ U, 0 ≤ d ⬝ᵥ ys v := fun v hv =>
    dotProduct_nonneg_of_nonneg hd (hfs.2 v hv).1
  have he : 0 ≤ e := le_trans (hD0 b hb) (hD b hb)
  have hw : ∀ l, 0 ≤ b l / μ l := fun l => div_nonneg (hUnn b hb l) (hμpos l).le
  have h1 : ∑ l ∈ J, b l / μ l * (d ⬝ᵥ ys (bstar l)) ≤ s * e := by
    have e1 : ∑ l ∈ J, b l / μ l * (d ⬝ᵥ ys (bstar l)) ≤ ∑ l ∈ J, b l / μ l * e :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hD _ (hbstar l).1) (hw l))
    have e2 : ∑ l ∈ J, b l / μ l * e = scaledSum μ J b * e := by
      rw [scaledSum, Finset.sum_mul]
    have e3 := hloop b hb
    have e4 : scaledSum μ J b * e ≤ s * e := mul_le_mul_of_nonneg_right e3 he
    linarith
  have h2 : 2 * s / K * ∑ k ∈ Finset.Icc 1 K, d ⬝ᵥ ys (u k) ≤ 2 * s * e := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0; simp; positivity
    · have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have e1 : ∑ k ∈ Finset.Icc 1 K, d ⬝ᵥ ys (u k) ≤ ∑ _k ∈ Finset.Icc 1 K, e :=
        Finset.sum_le_sum (fun k hk => hD _ (humem k hk))
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at e1
      have e2 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 2 * s / K)
      have e3 : 2 * s / K * (((K + 1 - 1 : ℕ) : ℝ) * e) = 2 * s * e := by
        rw [Nat.add_sub_cancel]; field_simp
      linarith
  have h3 : t = c ⬝ᵥ xs + e := by rw [hedef]; ring
  rw [h3]
  nlinarith

end P8c660a2b

open Matrix in
theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUconv : Convex ℝ U) (hUcpt : IsCompact U) (hUfull : (interior U).Nonempty)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), AffinePolicies.Simplex.Feasible A B U x y)
    (hA : ∀ i j, 0 ≤ A i j) :
    (∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
        AffinePolicies.Simplex.Feasible A B U x (AffinePolicies.Simplex.affinePolicy P q)) ∧
      AffinePolicies.Simplex.zAff A B c d U ≤ 3 * Real.sqrt m * AffinePolicies.Simplex.zAdapt A B c d U := by
  obtain ⟨p, hp⟩ := hUfull
  have hpU : p ∈ U := interior_subset hp
  have hUne : U.Nonempty := ⟨p, hpU⟩
  have hμex : ∀ j : Fin m, ∃ μj, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) μj :=
    fun j => (hUcpt.image (continuous_apply j)).exists_isGreatest (hUne.image _)
  choose μ hμ using hμex
  have hbex : ∀ j, ∃ bj, bj ∈ U ∧ bj j = μ j := fun j => by
    obtain ⟨bj, hbj, he⟩ := (hμ j).1
    exact ⟨bj, hbj, he⟩
  choose bstar hbstar using hbex
  have hμpos : ∀ j, 0 < μ j := P8c660a2b.mu_pos' U hUnn ⟨p, hp⟩ μ hμ
  have hbμ : ∀ b ∈ U, ∀ j, b j ≤ μ j := fun b hb j => (hμ j).2 ⟨b, hb, rfl⟩
  obtain ⟨K, u, hrun⟩ := P8c660a2b.exists_run U hUcpt hUne μ hμpos hbμ
  obtain ⟨xs, ys, hfs⟩ := hfeas
  have hfA := P8c660a2b.feas A B U hA hUnn μ hμpos hbμ bstar hbstar K u hrun xs ys hfs
  refine ⟨⟨_, _, _, hfA⟩, ?_⟩
  set P := AffinePolicies.SqrtBound.thmPolicyP ys bstar μ (AffinePolicies.SqrtBound.J1 μ u K)
    with hPdef
  set q := AffinePolicies.SqrtBound.thmPolicyq ys u K with hqdef
  set x3 := (3 * Real.sqrt m) • xs with hx3
  have hcont : Continuous (fun b : Fin m → ℝ =>
      c ⬝ᵥ x3 + d ⬝ᵥ AffinePolicies.Simplex.affinePolicy P q b) := by
    unfold AffinePolicies.Simplex.affinePolicy
    exact continuous_const.add (Continuous.dotProduct continuous_const
      ((Continuous.matrix_mulVec continuous_const continuous_id).add continuous_const))
  obtain ⟨b0, hb0U, hb0max⟩ := hUcpt.exists_isMaxOn hUne hcont.continuousOn
  have hT0 : (c ⬝ᵥ x3 + d ⬝ᵥ AffinePolicies.Simplex.affinePolicy P q b0) ∈
      {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
        AffinePolicies.Simplex.Feasible A B U x y ∧ AffinePolicies.Simplex.CostLE c d U x y t} :=
    ⟨x3, AffinePolicies.Simplex.affinePolicy P q, hfA, fun b hb => hb0max hb⟩
  have hbdd : BddBelow {t | ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
      AffinePolicies.Simplex.Feasible A B U x (AffinePolicies.Simplex.affinePolicy P q) ∧
      AffinePolicies.Simplex.CostLE c d U x (AffinePolicies.Simplex.affinePolicy P q) t} := by
    refine ⟨0, ?_⟩
    rintro t ⟨x, P', q', hf, hcst⟩
    have h0 := hcst p hpU
    have h1 := dotProduct_nonneg_of_nonneg hc hf.1
    have h2 := dotProduct_nonneg_of_nonneg hd (hf.2 p hpU).1
    linarith
  have key : ∀ t ∈ {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ),
      AffinePolicies.Simplex.Feasible A B U x y ∧ AffinePolicies.Simplex.CostLE c d U x y t},
      AffinePolicies.Simplex.zAff A B c d U ≤ 3 * Real.sqrt m * t := by
    rintro t ⟨x', y', hf', hc'⟩
    unfold AffinePolicies.Simplex.zAff
    apply csInf_le hbdd
    exact ⟨(3 * Real.sqrt m) • x', AffinePolicies.SqrtBound.thmPolicyP y' bstar μ
      (AffinePolicies.SqrtBound.J1 μ u K), AffinePolicies.SqrtBound.thmPolicyq y' u K,
      P8c660a2b.feas A B U hA hUnn μ hμpos hbμ bstar hbstar K u hrun x' y' hf',
      P8c660a2b.cost A B c d U hd hUnn μ hμpos hbμ bstar hbstar K u hrun x' y' hf' t hc'⟩
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have := key _ hT0
    rw [← h0] at this ⊢
    simpa using this
  · have h3 : 0 < 3 * Real.sqrt m := by linarith
    have : AffinePolicies.Simplex.zAff A B c d U / (3 * Real.sqrt m) ≤
        AffinePolicies.Simplex.zAdapt A B c d U := by
      unfold AffinePolicies.Simplex.zAdapt
      refine le_csInf ⟨_, hT0⟩ ?_
      intro t ht
      rw [div_le_iff₀ h3, mul_comm]
      exact key t ht
    rwa [div_le_iff₀ h3, mul_comm] at this
