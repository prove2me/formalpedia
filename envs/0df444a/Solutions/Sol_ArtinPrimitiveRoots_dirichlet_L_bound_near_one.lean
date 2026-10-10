-- Prove2me | solution 1 for ArtinPrimitiveRoots.dirichlet_L_bound_near_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T16:37:29.837984+00:00
-- url     : https://prove2.me/submissions/c16e4a93-d191-4a65-bbe9-2e2d5e12f397

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_log_phase_progression

section
/-! # L31L_Cont: the approximate formula (3.13) of [22] for Mathlib's `LFunction`

For a Dirichlet character `χ` mod `q`, a natural number `M ≥ 1` and `Re s > 0`, `Im s ≠ 0`:
`‖L(s, χ) − Σ_{1 ≤ n ≤ M} χ(n) n^{-s}‖ ≤ M^{1-σ}/‖s-1‖ + ‖s‖ (2q+1) M^{-σ}/σ`.

Route: the coefficients `χ(n)·1_{n > M}` have partial sums `G_M(t)`, and
`E_M(t) = G_M(t) − c_χ max(t − M, 0)` is bounded by `2q + 1` (periodicity). For `Re s > 1`,
Abel summation (`LSeries_eq_mul_integral'`) gives
`L(s, χ) = Σ_{n ≤ M} χ(n) n^{-s} + c_χ M^{1-s}/(s-1) + s·mellin E_M (-s)`; the right side is
holomorphic on `Re s > 0, s ≠ 1`, and the identity theorem on the quarter-planes
`{Re s > 0, ± Im s > 0}` extends the formula.
-/

namespace ArtinPrimitiveRoots.L31L

open Complex MeasureTheory Set Filter Topology Asymptotics Finset

variable {q : ℕ} [NeZero q]

/-- The mean value `c_χ = q⁻¹ Σ_a χ(a)`. -/
noncomputable def cχ (χ : DirichletCharacter ℂ q) : ℂ := (∑ a : ZMod q, χ a) / q

lemma norm_cχ_le (χ : DirichletCharacter ℂ q) : ‖cχ χ‖ ≤ 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  unfold cχ
  rw [norm_div, Complex.norm_natCast, div_le_one hq]
  calc ‖∑ a : ZMod q, χ a‖ ≤ ∑ a : ZMod q, ‖χ a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, (1 : ℝ) := sum_le_sum fun a _ => DirichletCharacter.norm_le_one χ a
    _ = q := by simp [ZMod.card]

/-- A block of `q` consecutive values sums to `q c_χ`. -/
lemma sum_block (χ : DirichletCharacter ℂ q) (A : ℕ) :
    ∑ k ∈ Ico A (A + q), χ (k : ZMod q) = q * cχ χ := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [cχ, mul_div_cancel₀ _ hq, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  calc ∑ j ∈ range q, χ ((A + j : ℕ) : ZMod q)
      = ∑ j ∈ range q, (fun a : ZMod q => χ ((A : ZMod q) + a)) (j : ZMod q) :=
        Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    _ = ∑ a : ZMod q, χ ((A : ZMod q) + a) := by
        refine Finset.sum_nbij' (fun j => (j : ZMod q)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
        · intro a _; exact Finset.mem_univ _
        · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
        · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
        · intro a _; exact ZMod.natCast_zmod_val a
        · intro a _; rfl
    _ = ∑ a : ZMod q, χ a := Fintype.sum_equiv (Equiv.addLeft ((A : ZMod q))) _ _ (fun a => rfl)

/-- Periodicity: `Σ_{A ≤ k < A+m} χ(k) = m c_χ + O(q)`. -/
lemma norm_sum_Ico_sub_le (χ : DirichletCharacter ℂ q) (m : ℕ) : ∀ A : ℕ,
    ‖∑ k ∈ Ico A (A + m), χ (k : ZMod q) - m * cχ χ‖ ≤ 2 * q := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A
    rcases lt_or_ge m q with hm | hm
    · calc ‖∑ k ∈ Ico A (A + m), χ (k : ZMod q) - m * cχ χ‖
          ≤ ‖∑ k ∈ Ico A (A + m), χ (k : ZMod q)‖ + ‖(m : ℂ) * cχ χ‖ := norm_sub_le _ _
        _ ≤ m + m := by
          gcongr
          · calc ‖∑ k ∈ Ico A (A + m), χ (k : ZMod q)‖
                ≤ ∑ k ∈ Ico A (A + m), ‖χ (k : ZMod q)‖ := norm_sum_le _ _
              _ ≤ ∑ _k ∈ Ico A (A + m), (1 : ℝ) :=
                  sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
              _ = m := by simp
          · rw [norm_mul, Complex.norm_natCast]
            exact mul_le_of_le_one_right (Nat.cast_nonneg _) (norm_cχ_le χ)
        _ ≤ 2 * q := by
          have : (m : ℝ) ≤ q := by exact_mod_cast hm.le
          linarith
    · have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have hsplit : ∑ k ∈ Ico A (A + m), χ (k : ZMod q) =
          ∑ k ∈ Ico A (A + q), χ (k : ZMod q) +
            ∑ k ∈ Ico (A + q) (A + q + (m - q)), χ (k : ZMod q) := by
        rw [Finset.sum_Ico_consecutive _ (by omega) (by omega)]
        congr 2; omega
      have := ih (m - q) (by omega) (A + q)
      rw [hsplit, sum_block]
      have e : (q : ℂ) * cχ χ + ∑ k ∈ Ico (A + q) (A + q + (m - q)), χ (k : ZMod q) - m * cχ χ =
          ∑ k ∈ Ico (A + q) (A + q + (m - q)), χ (k : ZMod q) - ((m - q : ℕ) : ℂ) * cχ χ := by
        rw [Nat.cast_sub hm]; ring
      rw [e]; exact this

/-- The coefficients `χ(n)` for `n > M`, and `0` otherwise. -/
noncomputable def aM (χ : DirichletCharacter ℂ q) (M n : ℕ) : ℂ := if M < n then χ n else 0

/-- Their partial sums. -/
noncomputable def GM (χ : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 ⌊t⌋₊, aM χ M k

/-- The bounded remainder `G_M(t) − c_χ max(t − M, 0)`. -/
noncomputable def EM (χ : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) : ℂ :=
  GM χ M t - cχ χ * ((max (t - M) 0 : ℝ) : ℂ)

omit [NeZero q] in
lemma GM_eq_zero (χ : DirichletCharacter ℂ q) (M : ℕ) {t : ℝ} (ht : t ≤ M) : GM χ M t = 0 := by
  unfold GM
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k ≤ ⌊t⌋₊ := (Finset.mem_Icc.mp hk).2
  have : ⌊t⌋₊ ≤ M := by
    rcases le_or_gt 0 t with h0 | h0
    · exact Nat.floor_le_of_le ht
    · simp [Nat.floor_eq_zero.mpr (by linarith : t < 1)]
  simp [aM, show ¬ M < k by omega]

lemma EM_eq_zero (χ : DirichletCharacter ℂ q) (M : ℕ) {t : ℝ} (ht : t ≤ M) : EM χ M t = 0 := by
  simp [EM, GM_eq_zero χ M ht, max_eq_right (by linarith : t - M ≤ 0)]

lemma norm_EM_le (χ : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) : ‖EM χ M t‖ ≤ 2 * q + 1 := by
  rcases le_or_gt t M with ht | ht
  · rw [EM_eq_zero χ M ht, norm_zero]; positivity
  · set n := ⌊t⌋₊ with hn
    have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg _) ht.le
    have hMn : M ≤ n := Nat.le_floor ht.le
    have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
    have htn : t < n + 1 := Nat.lt_floor_add_one t
    have hG : GM χ M t = ∑ k ∈ Ico (M + 1) (M + 1 + (n - M)), χ (k : ZMod q) := by
      unfold GM aM
      rw [← Finset.sum_filter]
      congr 1
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
    have hmax : max (t - M) 0 = ((n - M : ℕ) : ℝ) + (t - n) := by
      rw [max_eq_left (by linarith), Nat.cast_sub hMn]; ring
    have e : EM χ M t = (∑ k ∈ Ico (M + 1) (M + 1 + (n - M)), χ (k : ZMod q) -
        ((n - M : ℕ) : ℂ) * cχ χ) - cχ χ * ((t - n : ℝ) : ℂ) := by
      rw [EM, hG, hmax]; push_cast; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_sum_Ico_sub_le χ (n - M) (M + 1)
    have h2 : ‖cχ χ * ((t - n : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      calc ‖cχ χ‖ * (t - n) ≤ 1 * 1 :=
            mul_le_mul (norm_cχ_le χ) (by linarith) (by linarith) zero_le_one
        _ = 1 := by ring
    linarith

/-! ### Integrability -/

omit [NeZero q] in
lemma locallyIntegrable_GM (χ : DirichletCharacter ℂ q) (M : ℕ) :
    LocallyIntegrableOn (GM χ M) (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici (0 : ℝ)) :=
    (continuous_const.continuousOn).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (fun k : ℕ => aM χ M k) (m := 1) (a := 0)
    le_rfl h1
  simp only [one_mul] at h2
  exact h2.mono_set Ioi_subset_Ici_self

lemma continuous_maxM (M : ℕ) : Continuous fun t : ℝ => ((max (t - M) 0 : ℝ) : ℂ) := by
  fun_prop

lemma locallyIntegrable_EM (χ : DirichletCharacter ℂ q) (M : ℕ) :
    LocallyIntegrableOn (EM χ M) (Ioi (0 : ℝ)) := by
  have h2 : LocallyIntegrableOn (fun t : ℝ => cχ χ * ((max (t - M) 0 : ℝ) : ℂ)) (Ioi (0 : ℝ)) :=
    ((continuous_const.mul (continuous_maxM M)).continuousOn).locallyIntegrableOn
      measurableSet_Ioi
  exact (locallyIntegrable_GM χ M).sub h2

lemma isBigO_EM_top (χ : DirichletCharacter ℂ q) (M : ℕ) :
    (EM χ M) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (2 * q + 1) (Eventually.of_forall (fun t => ?_))
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_EM_le χ M t

lemma isBigO_zero_bot {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (M : ℕ) (hM : 1 ≤ M)
    (hf : ∀ t : ℝ, t ≤ M → f t = 0) (b : ℝ) :
    f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rw [hf t (by linarith [ht.2]), norm_zero]
  positivity

lemma mellinConv_EM (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (EM χ M) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_EM χ M) (isBigO_EM_top χ M) ?_
    (isBigO_zero_bot _ M hM (fun t ht => EM_eq_zero χ M ht) _) ?_
  · simpa using hs
  · simp

lemma differentiableAt_mellin_EM (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (fun z => mellin (EM χ M) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (EM χ M)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      (locallyIntegrable_EM χ M) (isBigO_EM_top χ M) (by simpa using hs)
      (isBigO_zero_bot _ M hM (fun t ht => EM_eq_zero χ M ht) _) (by simp)
  exact h.comp s differentiableAt_id.neg

lemma mellinConv_maxM (M : ℕ) (hM : 1 ≤ M) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ => ((max (t - M) 0 : ℝ) : ℂ)) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := -1) (b := -s.re - 1)
    ((continuous_maxM M).continuousOn.locallyIntegrableOn measurableSet_Ioi) ?_ ?_
    (isBigO_zero_bot _ M hM (fun t ht => by simp [max_eq_right (by linarith : t - M ≤ 0)]) _) ?_
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (M : ℝ)] with t ht
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), neg_neg,
      Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]
    exact max_le (by linarith) (by linarith)
  · simp; linarith
  · simp

/-! ### Splitting set integrals at a point where the integrand starts -/

lemma setIntegral_Ioi_eq {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ∀ t, t ≤ b → f t = 0) :
    ∫ t in Ioi a, f t = ∫ t in Ioi b, f t :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hab)
    (fun t ht => hf t (not_lt.mp ht.2))

/-! ### The formula for `Re s > 1` -/

/-- The right-hand side of (3.13), a holomorphic function on `Re s > 0`, `s ≠ 1`. -/
noncomputable def Fχ (χ : DirichletCharacter ℂ q) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s) + cχ χ * (M : ℂ) ^ (1 - s) / (s - 1) +
    s * mellin (EM χ M) (-s)

omit [NeZero q] in
lemma isBigO_aM (χ : DirichletCharacter ℂ q) (M : ℕ) :
    (fun n ↦ ∑ k ∈ Icc 1 n, ‖aM χ M k‖) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  simp only [Real.rpow_one, Real.norm_eq_abs]
  rw [abs_of_nonneg (sum_nonneg fun _ _ => norm_nonneg _), abs_of_nonneg (Nat.cast_nonneg _),
    one_mul]
  calc ∑ k ∈ Icc 1 n, ‖aM χ M k‖ ≤ ∑ _k ∈ Icc 1 n, (1 : ℝ) := by
        refine sum_le_sum fun k _ => ?_
        unfold aM; split_ifs
        · exact DirichletCharacter.norm_le_one χ _
        · simp
    _ = n := by simp

omit [NeZero q] in
lemma LSeries_split (χ : DirichletCharacter ℂ q) (M : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n) s = ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s) + LSeries (aM χ M) s := by
  have hχ : Summable (LSeries.term (fun n => χ n) s) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have ha : Summable (LSeries.term (aM χ M) s) :=
    LSeriesSummable_of_sum_norm_bigO (isBigO_aM χ M) zero_le_one hs
  unfold LSeries
  rw [← hχ.sum_add_tsum_nat_add (M + 1), ← ha.sum_add_tsum_nat_add (M + 1)]
  have h0 : ∑ i ∈ range (M + 1), LSeries.term (aM χ M) s i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ¬ M < i := by have := Finset.mem_range.mp hi; omega
    simp [LSeries.term, aM, this]
  have htail : ∀ i, LSeries.term (aM χ M) s (i + (M + 1)) =
      LSeries.term (fun n => χ n) s (i + (M + 1)) := by
    intro i
    simp [LSeries.term, aM, show M < i + (M + 1) by omega]
  have hfin : ∑ i ∈ range (M + 1), LSeries.term (fun n => χ n) s i =
      ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), LSeries.term_zero,
      zero_add]
    refine Finset.sum_congr (by ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega)
      fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    rw [LSeries.term_of_ne_zero hk0, Complex.cpow_neg, div_eq_mul_inv]
  rw [h0, zero_add, hfin]
  simp_rw [htail]

/-- The Abel-summation integral, split into the pole part and the remainder. -/
lemma integral_GM (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, aM χ M k) * (t : ℂ) ^ (-(s + 1)) =
      mellin (EM χ M) (-s) + cχ χ * ((M : ℂ) ^ (1 - s) / (s - 1) - (M : ℂ) ^ (1 - s) / s) := by
  have hs0 : 0 < s.re := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hE := mellinConv_EM χ M hM hs0
  have hX := mellinConv_maxM M hM hs
  -- pointwise decomposition
  have hpt : ∀ t : ℝ, (∑ k ∈ Icc 1 ⌊t⌋₊, aM χ M k) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s - 1) • EM χ M t +
        cχ χ * ((t : ℂ) ^ (-s - 1) • ((max (t - M) 0 : ℝ) : ℂ)) := by
    intro t
    rw [show -(s + 1) = -s - 1 by ring, smul_eq_mul, smul_eq_mul, EM, GM]; ring
  simp_rw [hpt]
  have hE1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • EM χ M t) (Ioi 1) :=
    hE.mono_set (Ioi_subset_Ioi zero_le_one)
  have hX1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • ((max (t - M) 0 : ℝ) : ℂ))
      (Ioi 1) := hX.mono_set (Ioi_subset_Ioi zero_le_one)
  rw [integral_add hE1 (hX1.const_mul _), integral_const_mul]
  congr 1
  · -- the remainder: `E_M` vanishes on `(0, 1]`
    rw [mellin, setIntegral_Ioi_eq zero_le_one (fun t ht => by
      rw [EM_eq_zero χ M (by linarith), smul_zero])]
  · congr 1
    -- `∫_M^∞ (t - M) t^{-s-1} dt`
    rw [setIntegral_Ioi_eq hM1 (fun t ht => by
      simp [max_eq_right (by linarith : t - M ≤ 0)])]
    have hcongr : ∀ t ∈ Ioi (M : ℝ), (t : ℂ) ^ (-s - 1) • ((max (t - M) 0 : ℝ) : ℂ) =
        (t : ℂ) ^ (-s) - (M : ℂ) * (t : ℂ) ^ (-s - 1) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := by
        have : (0 : ℝ) < t := lt_trans hM0 ht
        exact_mod_cast this.ne'
      rw [max_eq_left (by linarith [show (M : ℝ) < t from ht]), smul_eq_mul]
      have : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * t := by
        rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one, div_mul_cancel₀ _ ht0]
      rw [this]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    have hi1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (M : ℝ)) :=
      integrableOn_Ioi_cpow_of_lt (by simp; linarith) hM0
    have hi2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Ioi (M : ℝ)) :=
      integrableOn_Ioi_cpow_of_lt (by simp; linarith) hM0
    rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul,
      integral_Ioi_cpow_of_lt (by simp; linarith) hM0,
      integral_Ioi_cpow_of_lt (by simp; linarith) hM0]
    have hs1 : s - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs0' : s ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hpow : (M : ℂ) * (M : ℂ) ^ (-s) = (M : ℂ) ^ (1 - s) := by
      rw [show (1 : ℂ) - s = -s + 1 by ring, Complex.cpow_add _ _ hMc, Complex.cpow_one]; ring
    rw [show -s - 1 + 1 = -s by ring, show -s + 1 = 1 - s by ring]
    have h1s : (1 - s) ≠ 0 := by
      intro h; apply hs1; linear_combination -h
    simp only [Complex.ofReal_natCast]
    rw [← hpow]
    field_simp
    ring

lemma LFunction_eq_Fχ_of_one_lt (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = Fχ χ M s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries_split χ M hs,
    LSeries_eq_mul_integral' (aM χ M) zero_le_one hs (isBigO_aM χ M), integral_GM χ M hM hs, Fχ]
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs0' : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

lemma differentiableAt_Fχ (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ (Fχ χ M) s := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast (show 0 < M by omega).ne'
  unfold Fχ
  refine ((DifferentiableAt.fun_sum fun n hn => ?_).add ?_).add ?_
  · have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by simp at hn; omega
      exact_mod_cast this
    exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _
  · refine ((differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl hMc)
      |>.const_mul _).div (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs1)
  · exact differentiableAt_id.mul (differentiableAt_mellin_EM χ M hM hs)

/-- The identity theorem on an open preconnected set inside `Re s > 0`, `s ≠ 1`, meeting
`Re s > 1`. -/
lemma LFunction_eq_Fχ_on (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) (U : Set ℂ)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hU : ∀ z ∈ U, 0 < z.re ∧ z ≠ 1) (z₀ : ℂ)
    (hz₀ : z₀ ∈ U) (hz₀1 : 1 < z₀.re) : EqOn (DirichletCharacter.LFunction χ) (Fχ χ M) U := by
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (hU z hz).2)).differentiableWithinAt)
      hUo
  have hF : AnalyticOnNhd ℂ (Fχ χ M) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_Fχ χ M hM (hU z hz).1 (hU z hz).2).differentiableWithinAt) hUo
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 z₀] Fχ χ M := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz₀1] with z hz
    exact LFunction_eq_Fχ_of_one_lt χ M hM hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hF hUc hz₀ hev

lemma LFunction_eq_Fχ (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) (him : s.im ≠ 0) : DirichletCharacter.LFunction χ s = Fχ χ M s := by
  rcases lt_or_gt_of_ne him with h | h
  · set U : Set ℂ := {z | 0 < z.re} ∩ {z | z.im < 0}
    have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_im continuous_const)
    have hUc : IsPreconnected U :=
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
    refine LFunction_eq_Fχ_on χ M hM U hUo hUc (fun z hz => ⟨hz.1, fun h1 => ?_⟩) (2 - I)
      ⟨by simp, by simp⟩ (by norm_num) ⟨hs, h⟩
    have := hz.2; rw [h1] at this; simp at this
  · set U : Set ℂ := {z | 0 < z.re} ∩ {z | 0 < z.im}
    have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im)
    have hUc : IsPreconnected U :=
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
    refine LFunction_eq_Fχ_on χ M hM U hUo hUc (fun z hz => ⟨hz.1, fun h1 => ?_⟩) (2 + I)
      ⟨by simp, by simp⟩ (by norm_num) ⟨hs, h⟩
    have := hz.2; rw [h1] at this; simp at this

/-! ### The bound -/

lemma norm_mellin_EM_le (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) : ‖mellin (EM χ M) (-s)‖ ≤ (2 * q + 1) * (M : ℝ) ^ (-s.re) / s.re := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlt : (-s.re - 1 : ℝ) < -1 := by linarith
  have hconv := mellinConv_EM χ M hM hs
  set u : ℝ → ℝ := fun t => t ^ (-s.re - 1) * ‖EM χ M t‖ with hu
  have hIA : IntegrableOn u (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  have hstep1 : ‖mellin (EM χ M) (-s)‖ ≤ ∫ t in Ioi (0 : ℝ), u t := by
    rw [mellin]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  have hsplit : ∫ t in Ioi (0 : ℝ), u t = ∫ t in Ioi (M : ℝ), u t :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi hM0.le) (fun t ht => by
        simp [hu, EM_eq_zero χ M (not_lt.mp ht.2)])
  have hmaj : IntegrableOn (fun t : ℝ => (2 * q + 1 : ℝ) * t ^ (-s.re - 1)) (Ioi (M : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hlt hM0).const_mul _
  have hstep : ∫ t in Ioi (M : ℝ), u t ≤ ∫ t in Ioi (M : ℝ), (2 * q + 1 : ℝ) * t ^ (-s.re - 1) := by
    refine setIntegral_mono_on (hIA.mono_set (Ioi_subset_Ioi hM0.le)) hmaj
      measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans hM0 ht
    calc u t ≤ t ^ (-s.re - 1) * (2 * q + 1 : ℝ) :=
          mul_le_mul_of_nonneg_left (norm_EM_le χ M t) (Real.rpow_nonneg ht0.le _)
      _ = (2 * q + 1 : ℝ) * t ^ (-s.re - 1) := by ring
  have hval : ∫ t in Ioi (M : ℝ), (2 * q + 1 : ℝ) * t ^ (-s.re - 1) =
      (2 * q + 1) * (M : ℝ) ^ (-s.re) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hM0,
      show (-s.re - 1 + 1 : ℝ) = -s.re by ring]
    field_simp
  linarith

/-- **(3.13)** for Mathlib's `LFunction`, every Dirichlet character (no primitivity, the
principal character included), `Re s > 0`, `Im s ≠ 0`. -/
theorem norm_LFunction_sub_le (χ : DirichletCharacter ℂ q) (M : ℕ) (hM : 1 ≤ M) {s : ℂ}
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖ ≤
      (M : ℝ) ^ (1 - s.re) / ‖s - 1‖ + ‖s‖ * ((2 * q + 1) * (M : ℝ) ^ (-s.re) / s.re) := by
  rw [LFunction_eq_Fχ χ M hM hs him, Fχ, add_assoc, add_sub_cancel_left]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have : (1 - s).re = 1 - s.re := by simp
    rw [this]
    have h1 := norm_cχ_le χ
    have h2 : 0 ≤ (M : ℝ) ^ (1 - s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    gcongr
    calc ‖cχ χ‖ * (M : ℝ) ^ (1 - s.re) ≤ 1 * (M : ℝ) ^ (1 - s.re) := by gcongr
      _ = _ := one_mul _
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_mellin_EM_le χ M hM hs) (norm_nonneg _)

end ArtinPrimitiveRoots.L31L
end

section
/-! # L31L_Sums: finite Dirichlet polynomials near `Re s = 1`

* `norm_sum_le_trivial`: `‖Σ_{n ≤ M} χ(n) n^{-s}‖ ≤ M^δ (1 + log M)` when `Re s ≥ 1 − δ`.
* `abel_weight`: Abel summation against a nonincreasing nonnegative weight.
* `block_bound`: a block `(A, B]`, `B ≤ 2A`, of `Σ χ(n) n^{-s}`, given bounds for the
  progression sums `Σ_{n ∈ J, n ≡ a (q)} n^{-i Im s}` (the shape of `log_phase_progression`).
* `sum_Ioc_dyadic`: splitting `(n₀, min(n₀ 2^K, M)]` into dyadic blocks.
-/

namespace ArtinPrimitiveRoots.L31L

open Complex Finset

/-- The trivial bound. -/
lemma norm_sum_le_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) (s : ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hs : 1 - δ ≤ s.re) :
    ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖ ≤ (M : ℝ) ^ δ * (1 + Real.log M) := by
  have hterm : ∀ n ∈ Icc 1 M, ‖χ n * (n : ℂ) ^ (-s)‖ ≤ (M : ℝ) ^ δ * (n : ℝ)⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, neg_re]
    calc ‖χ n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (δ - 1) :=
          mul_le_mul (DirichletCharacter.norm_le_one χ _)
            (Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)) (by positivity) zero_le_one
      _ = (n : ℝ) ^ δ * (n : ℝ)⁻¹ := by
          rw [one_mul, Real.rpow_sub hn0, Real.rpow_one, div_eq_mul_inv]
      _ ≤ (M : ℝ) ^ δ * (n : ℝ)⁻¹ := by
          gcongr
  calc ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Icc 1 M, ‖χ n * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 M, (M : ℝ) ^ δ * (n : ℝ)⁻¹ := sum_le_sum hterm
    _ = (M : ℝ) ^ δ * ∑ n ∈ Icc 1 M, (n : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ (M : ℝ) ^ δ * (1 + Real.log M) := by
        gcongr
        have h := harmonic_le_one_add_log M
        rw [harmonic_eq_sum_Icc] at h
        push_cast at h
        exact h

/-- Abel summation identity against a weight. -/
lemma abel_identity (f : ℕ → ℂ) (w : ℕ → ℝ) (A : ℕ) : ∀ B : ℕ, A ≤ B →
    ∑ n ∈ Ioc A B, f n * (w n : ℂ) =
      (∑ n ∈ Ioc A B, f n) * (w B : ℂ) +
        ∑ m ∈ Ico A B, (∑ n ∈ Ioc A m, f n) * ((w m - w (m + 1) : ℝ) : ℂ) := by
  intro B hB
  induction B, hB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ioc_succ_top hAB, Finset.sum_Ioc_succ_top hAB,
      Finset.sum_Ico_succ_top hAB, ih]
    push_cast; ring

/-- Telescoping of real differences. -/
lemma telescope_real (w : ℕ → ℝ) (A : ℕ) : ∀ B : ℕ, A ≤ B →
    ∑ m ∈ Ico A B, (w m - w (m + 1)) = w A - w B := by
  intro B hB
  induction B, hB using Nat.le_induction with
  | base => simp
  | succ B hAB ih => rw [Finset.sum_Ico_succ_top hAB, ih]; ring

/-- Abel summation against a nonincreasing nonnegative weight. -/
lemma abel_weight (f : ℕ → ℂ) (w : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B)
    (hw : ∀ n, A ≤ n → n < B → w (n + 1) ≤ w n) (hw0 : 0 ≤ w B) (S : ℝ)
    (hS : ∀ m, A ≤ m → m ≤ B → ‖∑ n ∈ Ioc A m, f n‖ ≤ S) :
    ‖∑ n ∈ Ioc A B, f n * (w n : ℂ)‖ ≤ S * w A := by
  rw [abel_identity f w A B hAB]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(∑ n ∈ Ioc A B, f n) * (w B : ℂ)‖ ≤ S * w B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hS B hAB le_rfl) hw0
  have h2 : ‖∑ m ∈ Ico A B, (∑ n ∈ Ioc A m, f n) * ((w m - w (m + 1) : ℝ) : ℂ)‖ ≤
      S * (w A - w B) := by
    rw [← telescope_real w A B hAB, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
    have hm' := Finset.mem_Ico.mp hm
    have hd : 0 ≤ w m - w (m + 1) := by linarith [hw m hm'.1 hm'.2]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right (hS m hm'.1 hm'.2.le) hd
  linarith

/-- Splitting a sum into residue classes. -/
lemma sum_residues' (s : Finset ℕ) (k : ℕ) (hk : 0 < k) (f : ℕ → ℂ) :
    ∑ t ∈ s, f t = ∑ b ∈ range k, ∑ t ∈ s.filter (fun t => t ≡ b [MOD k]), f t := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => t % k) (t := range k)
    (fun t _ => Finset.mem_range.2 (Nat.mod_lt t hk))]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b % k = b := Nat.mod_eq_of_lt (Finset.mem_range.1 hb)
  congr 1
  ext t
  simp only [Finset.mem_filter, Nat.ModEq, hb']

/-- `n^{-s} = n^{i(-Im s)} · n^{-Re s}` for `n ≥ 1`. -/
lemma natCast_cpow_neg_eq (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (n : ℂ) ^ (-s) = (n : ℂ) ^ (I * (-s.im : ℝ)) * (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hn0]
  congr 1
  apply Complex.ext <;> simp

open Classical in
/-- A block `(A, B]` with `B ≤ 2A` of the Dirichlet polynomial, from bounds `β` for the
progression sums of `n^{i u}`, `u = −Im s`, over subintervals of `[A, 2A]`. -/
lemma block_bound {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (s : ℂ) (hσ : 0 ≤ s.re)
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ 2 * A) (β : ℝ)
    (hP : ∀ a : ℕ, ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc (A : ℝ) (2 * A) →
      ‖∑ n ∈ (range (⌊2 * (A : ℝ)⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
          (if (n : ℝ) ∈ J then (n : ℂ) ^ (I * (-s.im : ℝ)) else 0)‖ ≤ β) :
    ‖∑ n ∈ Ioc A B, χ n * (n : ℂ) ^ (-s)‖ ≤ q * β * (A : ℝ) ^ (-s.re) := by
  have hfloor : ⌊2 * (A : ℝ)⌋₊ = 2 * A := by
    rw [show (2 * (A : ℝ)) = ((2 * A : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  set u : ℝ := -s.im
  have hrw : ∀ n ∈ Ioc A B, χ n * (n : ℂ) ^ (-s) =
      (χ n * (n : ℂ) ^ (I * (u : ℂ))) * (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) := by
    intro n hn
    rw [natCast_cpow_neg_eq n (by have := (Finset.mem_Ioc.mp hn).1; omega) s]; ring
  rw [Finset.sum_congr rfl hrw]
  refine abel_weight (fun n => χ n * (n : ℂ) ^ (I * (u : ℂ))) (fun n => (n : ℝ) ^ (-s.re)) A B
    hAB (fun n hn _ => ?_) (Real.rpow_nonneg (Nat.cast_nonneg _) _) _ (fun m hAm hmB => ?_)
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hA hn
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by push_cast; linarith) (by linarith)
  · -- the partial sum over `(A, m]`, split into residue classes
    set J : Set ℝ := Set.Ioc (A : ℝ) m
    have hJ : J.OrdConnected := Set.ordConnected_Ioc
    have hJsub : J ⊆ Set.Icc (A : ℝ) (2 * A) := by
      intro y hy
      have : (m : ℝ) ≤ 2 * A := by exact_mod_cast (le_trans hmB hB)
      exact ⟨hy.1.le, le_trans hy.2 this⟩
    have e1 : ∑ n ∈ Ioc A m, χ n * (n : ℂ) ^ (I * (u : ℂ)) =
        ∑ n ∈ range (⌊2 * (A : ℝ)⌋₊ + 1),
          (if (n : ℝ) ∈ J then χ n * (n : ℂ) ^ (I * (u : ℂ)) else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range, hfloor, J, Set.mem_Ioc,
        Nat.cast_lt, Nat.cast_le]
      omega
    rw [e1, sum_residues' _ q hq]
    have e2 : ∀ b ∈ range q,
        ∑ n ∈ (range (⌊2 * (A : ℝ)⌋₊ + 1)).filter (fun n => n ≡ b [MOD q]),
          (if (n : ℝ) ∈ J then χ n * (n : ℂ) ^ (I * (u : ℂ)) else 0) =
        χ b * ∑ n ∈ (range (⌊2 * (A : ℝ)⌋₊ + 1)).filter (fun n => n ≡ b [MOD q]),
          (if (n : ℝ) ∈ J then (n : ℂ) ^ (I * (u : ℂ)) else 0) := by
      intro b _
      rw [mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnb : (n : ZMod q) = (b : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff n b q).mpr (Finset.mem_filter.mp hn).2
      split_ifs <;> simp [hnb]
    rw [Finset.sum_congr rfl e2]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ range q, ‖χ b * ∑ n ∈ (range (⌊2 * (A : ℝ)⌋₊ + 1)).filter
            (fun n => n ≡ b [MOD q]), (if (n : ℝ) ∈ J then (n : ℂ) ^ (I * (u : ℂ)) else 0)‖
        ≤ ∑ _b ∈ range q, 1 * β := by
          refine sum_le_sum fun b _ => ?_
          rw [norm_mul]
          refine mul_le_mul (DirichletCharacter.norm_le_one χ _) (le_of_eq_of_le ?_ (hP b J hJ hJsub))
            (norm_nonneg _) zero_le_one
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          congr
      _ = q * β := by simp

/-- Splitting `(n₀, min(n₀ 2^K, M)]` into the blocks `(min(n₀ 2^k, M), min(n₀ 2^{k+1}, M)]`. -/
lemma sum_Ioc_dyadic (g : ℕ → ℂ) (n₀ M : ℕ) (h : n₀ ≤ M) : ∀ K : ℕ,
    ∑ n ∈ Ioc n₀ (min (n₀ * 2 ^ K) M), g n =
      ∑ k ∈ range K, ∑ n ∈ Ioc (min (n₀ * 2 ^ k) M) (min (n₀ * 2 ^ (k + 1)) M), g n := by
  intro K
  induction K with
  | zero => simp [min_eq_left h]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Ioc_consecutive]
    · have : n₀ ≤ n₀ * 2 ^ K := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    · have : n₀ * 2 ^ K ≤ n₀ * 2 ^ (K + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
        (by norm_num) (by omega))
      omega

end ArtinPrimitiveRoots.L31L
end

section
/-! # L31L_Main: `dirichlet_L_bound_near_one` ([22] Lemma 3.4)

With `L = log x = e^T`, `δ = 10T⁴/L`:
* `|v| ≤ exp(L/(2T²))`: (3.13) with `M = ⌊exp(2L/T²)⌋` and the trivial bound (`range_small`);
* `|v| > exp(L/(2T²))`: (3.13) with `M = ⌊x⁵⌋`; the terms `n ≤ ⌈exp(L/T²)⌉` trivially, the
  dyadic blocks above by `log_phase_progression` and Abel summation (`range_large`).
-/

namespace ArtinPrimitiveRoots.L31L

open Real Finset

lemma ev_pow_le_exp (a : ℝ) (n : ℕ) : ∀ᶠ T in Filter.atTop, a * T ^ n ≤ exp T := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hpos : (0 : ℝ) < 1 / (|a| + 1) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hpos), Filter.eventually_ge_atTop (0 : ℝ)]
    with T hT hT0
  have hTn : 0 ≤ T ^ n := pow_nonneg hT0 n
  have h1 : (|a| + 1) * (T ^ n * exp (-T)) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hT; linarith
  have hexp : exp (-T) * exp T = 1 := by rw [← exp_add]; simp
  calc a * T ^ n ≤ (|a| + 1) * T ^ n :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self a]) hTn
    _ = (|a| + 1) * (T ^ n * exp (-T)) * exp T := by
        linear_combination (-(|a| + 1) * T ^ n) * hexp
    _ ≤ 1 * exp T := mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp T := one_mul _

/-- `⌊Y⌋₊` for `Y ≥ 2`. -/
lemma floor_facts {Y : ℝ} (hY : 2 ≤ Y) :
    1 ≤ ⌊Y⌋₊ ∧ (⌊Y⌋₊ : ℝ) ≤ Y ∧ log Y - 1 ≤ log ⌊Y⌋₊ := by
  have hlt := Nat.lt_floor_add_one Y
  have h1 : (1 : ℝ) ≤ ⌊Y⌋₊ := by linarith
  refine ⟨by exact_mod_cast h1, Nat.floor_le (by linarith), ?_⟩
  have hhalf : Y / 2 ≤ ⌊Y⌋₊ := by linarith
  have := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (by linarith) (by norm_num)] at this
  have := Real.log_two_lt_d9
  linarith

lemma rpow_le_exp_of_log_le {M r δ ℓ : ℝ} (hM : 1 ≤ M) (hr : r ≤ δ) (hδ : 0 ≤ δ)
    (hℓ : log M ≤ ℓ) : M ^ r ≤ exp (δ * ℓ) := by
  calc M ^ r ≤ M ^ δ := Real.rpow_le_rpow_of_exponent_le hM hr
    _ = exp (log M * δ) := Real.rpow_def_of_pos (by linarith) _
    _ ≤ exp (δ * ℓ) := by
        rw [mul_comm]; exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left hℓ hδ)

lemma rpow_neg_le_exp {M σ σ₀ ℓ : ℝ} (hM : 0 < M) (hσ : σ₀ ≤ σ) (hσ₀ : 0 ≤ σ₀)
    (hℓ : ℓ ≤ log M) (hℓ0 : 0 ≤ ℓ) : M ^ (-σ) ≤ exp (-(σ₀ * ℓ)) := by
  rw [Real.rpow_def_of_pos hM]
  apply exp_le_exp.mpr
  have : σ₀ * ℓ ≤ σ * log M := mul_le_mul hσ hℓ hℓ0 (by linarith)
  linarith

/-- The remainder of (3.13), assembled from exponential bounds of its factors. -/
lemma err_le {q : ℕ} {s : ℂ} {M a b c : ℝ} (hσ : 4 / 5 ≤ s.re) (hM : 0 ≤ M)
    (hs : ‖s‖ ≤ exp a) (hq : 2 * (q : ℝ) + 1 ≤ exp b) (hMc : M ^ (-s.re) ≤ exp c) :
    ‖s‖ * ((2 * q + 1) * M ^ (-s.re) / s.re) ≤ exp (a + b + c + 1) := by
  have hσ0 : 0 < s.re := by linarith
  have h1 : 1 / s.re ≤ exp 1 := by
    have : 1 / s.re ≤ 5 / 4 := by rw [div_le_iff₀ hσ0]; linarith
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [exp_add, exp_add, exp_add]
  have hMn : 0 ≤ M ^ (-s.re) := Real.rpow_nonneg hM _
  calc ‖s‖ * ((2 * q + 1) * M ^ (-s.re) / s.re)
      = ‖s‖ * (2 * q + 1) * M ^ (-s.re) * (1 / s.re) := by ring
    _ ≤ exp a * exp b * exp c * exp 1 := by
        gcongr

lemma norm_le_of_sub {L S : ℂ} : ‖L‖ ≤ ‖S‖ + ‖L - S‖ := by
  calc ‖L‖ = ‖S + (L - S)‖ := by ring_nf
    _ ≤ ‖S‖ + ‖L - S‖ := norm_add_le _ _

/-- Elementary consequences of the size conditions on `T`. -/
lemma T_facts {T : ℝ} (hT2 : 2 ≤ T) (hT50 : 50 * T ^ 4 ≤ exp T) :
    0 < T ∧ T ^ 2 ≤ exp T ∧ 10 * (T ^ 4 / exp T) ≤ 1 / 5 ∧ 1 ≤ exp T / T ^ 2 ∧
      4 ≤ T ^ 2 ∧ T ≤ T ^ 2 ∧ T ≤ T ^ 3 ∧ 16 ≤ T ^ 4 := by
  have hT0 : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have heT := exp_pos T
  have h4 : (4 : ℝ) ≤ T ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 2; norm_num at this; linarith
  have h16 : (16 : ℝ) ≤ T ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 4; norm_num at this; linarith
  have hT22 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ hT1 (by norm_num)
  have hT2e : T ^ 2 ≤ exp T := by linarith
  refine ⟨hT0, hT2e, ?_, ?_, h4, le_self_pow₀ hT1 (by norm_num), le_self_pow₀ hT1 (by norm_num),
    h16⟩
  · rw [mul_div_assoc', div_le_iff₀ heT]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

lemma sigma_facts {s : ℂ} {δ : ℝ} (hσ : |s.re - 1| ≤ δ) (hδ5 : δ ≤ 1 / 5) :
    1 - δ ≤ s.re ∧ 1 - s.re ≤ δ ∧ 4 / 5 ≤ s.re ∧ s.re ≤ 2 := by
  have := abs_le.mp hσ
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The range `|v| ≤ exp(L/(2T²))`. -/
lemma range_small (C T : ℝ) (hC : 0 < C) (hT2 : 2 ≤ T) (hT50 : 50 * T ^ 4 ≤ exp T)
    (hTC : (C + 6) * T ^ 3 ≤ exp T) (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ exp (C * T))
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hσ : |s.re - 1| ≤ 10 * (T ^ 4 / exp T))
    (hv1 : 1 / 2 ≤ |s.im|) (hv2 : |s.im| ≤ exp (exp T / (2 * T ^ 2))) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ exp (100 * T ^ 2) := by
  obtain ⟨hT0, hT2e, hδ5, hE1, hT4sq, hTT2, hTT3, hT16⟩ := T_facts hT2 hT50
  set δ := 10 * (T ^ 4 / exp T) with hδdef
  have heT : 0 < exp T := exp_pos T
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨hσ1, hσ2, hσ45, hσ2'⟩ := sigma_facts hσ hδ5
  set E := exp T / T ^ 2 with hEdef
  have hE2 : exp T / (2 * T ^ 2) = E / 2 := by rw [hEdef]; field_simp
  rw [hE2] at hv2
  have hδE : δ * (2 * E) = 20 * T ^ 2 := by
    rw [hδdef, hEdef]; field_simp; ring
  -- the cut-off `M = ⌊exp(2E)⌋`
  have hY : (2 : ℝ) ≤ exp (2 * E) := by
    have := Real.add_one_le_exp (2 * E); linarith
  obtain ⟨hM1, hMY, hMlog⟩ := floor_facts hY
  set M := ⌊exp (2 * E)⌋₊ with hMdef
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_exp] at hMlog
  have hlogM : log M ≤ 2 * E := by
    calc log M ≤ log (exp (2 * E)) := Real.log_le_log hM0 hMY
      _ = 2 * E := Real.log_exp _
  -- the main sum
  have hP1 : ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖ ≤ exp (21 * T ^ 2) := by
    refine (norm_sum_le_trivial χ M s δ hδ0 hσ1).trans ?_
    have h1 : (M : ℝ) ^ δ ≤ exp (20 * T ^ 2) := by
      rw [← hδE]; exact rpow_le_exp_of_log_le hM1' le_rfl hδ0 hlogM
    have h2 : 1 + log M ≤ exp (T ^ 2) := by
      have hE' : 2 * E ≤ exp T / 2 := by
        rw [hEdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
        have := mul_le_mul_of_nonneg_left hT4sq heT.le
        linarith
      have h3 : exp T ≤ exp (T ^ 2) := exp_le_exp.mpr hTT2
      have h4 : (2 : ℝ) ≤ exp T := by have := Real.add_one_le_exp T; linarith
      linarith
    calc (M : ℝ) ^ δ * (1 + log M) ≤ exp (20 * T ^ 2) * exp (T ^ 2) :=
          mul_le_mul h1 h2 (by linarith [Real.log_nonneg hM1']) (exp_pos _).le
      _ = exp (21 * T ^ 2) := by rw [← exp_add]; ring_nf
  -- the pole term
  have hP2 : (M : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 2 * exp (20 * T ^ 2) := by
    have hn : 1 / 2 ≤ ‖s - 1‖ := le_trans hv1 (by simpa using Complex.abs_im_le_norm (s - 1))
    have h1 : (M : ℝ) ^ (1 - s.re) ≤ exp (20 * T ^ 2) := by
      rw [← hδE]; exact rpow_le_exp_of_log_le hM1' hσ2 hδ0 hlogM
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 2 * exp (20 * T ^ 2))
    linarith
  -- the remainder
  have hP3 : ‖s‖ * ((2 * q + 1) * (M : ℝ) ^ (-s.re) / s.re) ≤ 1 := by
    have he2 : (3 : ℝ) ≤ exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have hs : ‖s‖ ≤ exp (E / 2 + 2) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im s
      have h2 : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, hσ2'⟩
      have h3 : 1 ≤ exp (E / 2) := Real.one_le_exp (by linarith)
      have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos (E / 2)).le
      rw [exp_add]; linarith
    have hq' : 2 * (q : ℝ) + 1 ≤ exp (C * T + 2) := by
      have h3 : 1 ≤ exp (C * T) := Real.one_le_exp (by positivity)
      have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos (C * T)).le
      rw [exp_add]; linarith
    have hMs : (M : ℝ) ^ (-s.re) ≤ exp (-(4 / 5 * (2 * E - 1))) :=
      rpow_neg_le_exp hM0 hσ45 (by norm_num) hMlog (by linarith)
    refine (err_le hσ45 hM0.le hs hq' hMs).trans (le_of_le_of_eq (exp_le_exp.mpr ?_) exp_zero)
    have h5 : (C + 6) * T ≤ E := by
      rw [hEdef, le_div_iff₀ (by positivity)]
      have : (C + 6) * T * T ^ 2 = (C + 6) * T ^ 3 := by ring
      linarith
    have h6 : C * T + 6 * T ≤ E := by linarith [show (C + 6) * T = C * T + 6 * T by ring]
    linarith
  -- assemble
  have him : s.im ≠ 0 := by intro h; rw [h] at hv1; norm_num at hv1
  have hsub := norm_LFunction_sub_le χ M hM1 (s := s) (by linarith) him
  refine (norm_le_of_sub (S := ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s))).trans ?_
  have : exp (21 * T ^ 2) + (2 * exp (20 * T ^ 2) + 1) ≤ exp (100 * T ^ 2) := by
    have h1 : exp (20 * T ^ 2) ≤ exp (21 * T ^ 2) := exp_le_exp.mpr (by linarith)
    have h2 : 1 ≤ exp (21 * T ^ 2) := Real.one_le_exp (by positivity)
    have h3 : exp (21 * T ^ 2) * exp 2 ≤ exp (100 * T ^ 2) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
    have he2 : (4 : ℝ) ≤ exp 2 := by
      have h6 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have h7 : (2 : ℝ) ≤ exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      rw [h6]
      have := mul_le_mul h7 h7 (by norm_num) (exp_pos 1).le
      linarith
    have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos (21 * T ^ 2)).le
    linarith
  linarith


open Classical in
/-- The range `|v| > exp(L/(2T²))`, given `log_phase_progression` at this `x` (hypothesis `hLP`). -/
lemma range_large (C T C₃ K₃ : ℝ) (n : ℕ) (hC : 0 < C) (hT2 : 2 ≤ T)
    (hT50 : 50 * T ^ 4 ≤ exp T) (hT100 : 100 * T ^ 6 ≤ exp T) (hTC : (C + 6) * T ^ 3 ≤ exp T)
    (hn : C₃ ≤ n) (hTb : (log (11 * |K₃| + 1) + 51) * T ^ (n + 4) ≤ exp T)
    (q : ℕ) [NeZero q] (hq : (q : ℝ) ≤ exp (C * T))
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hσ : |s.re - 1| ≤ 10 * (T ^ 4 / exp T))
    (hv1 : exp (exp T / (2 * T ^ 2)) < |s.im|) (hv2 : |s.im| ≤ 3 * exp (3 * exp T))
    (hLP : ∀ N : ℝ, exp (exp T / T ^ 2) ≤ N → N ≤ 2 * exp (5 * exp T) →
      ∀ a : ℕ, ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc N (2 * N) →
        ‖∑ m ∈ (range (⌊2 * N⌋₊ + 1)).filter (fun m => m ≡ a [MOD q]),
            (if (m : ℝ) ∈ J then (m : ℂ) ^ (Complex.I * ((-s.im : ℝ) : ℂ)) else 0)‖ ≤
          K₃ * (N / q) * exp (-(exp T / T ^ C₃))) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ exp (100 * T ^ 2) := by
  obtain ⟨hT0, hT2e, hδ5, hE1, hT4sq, hTT2, hTT3, hT16⟩ := T_facts hT2 hT50
  set δ := 10 * (T ^ 4 / exp T) with hδdef
  have heT : 0 < exp T := exp_pos T
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨hσ1, hσ2, hσ45, hσ2'⟩ := sigma_facts hσ hδ5
  have hT4 : (16 : ℝ) ≤ T ^ 4 := hT16
  have heT800 : (800 : ℝ) ≤ exp T := by linarith
  set E := exp T / T ^ 2 with hEdef
  have hE2 : exp T / (2 * T ^ 2) = E / 2 := by rw [hEdef]; field_simp
  rw [hE2] at hv1
  have hE4 : 4 * E ≤ exp T := by
    rw [hEdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hT4sq heT.le
    linarith
  have hδ5L : δ * (5 * exp T) = 50 * T ^ 4 := by rw [hδdef]; field_simp; ring
  have hδE : δ * (E + 1) ≤ 10 * T ^ 2 + 1 := by
    have : δ * E = 10 * T ^ 2 := by rw [hδdef, hEdef]; field_simp; try ring
    have : δ * (E + 1) = δ * E + δ := by ring
    linarith
  have he1 : (2.7 : ℝ) ≤ exp 1 := by have := Real.exp_one_gt_d9; linarith
  have he2 : (5 : ℝ) ≤ exp 2 := by
    have h6 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [h6]
    have := mul_le_mul he1 he1 (by norm_num) (exp_pos 1).le
    linarith
  -- the cut-off `M = ⌊x⁵⌋`
  have hY : (2 : ℝ) ≤ exp (5 * exp T) := by
    have := Real.add_one_le_exp (5 * exp T); linarith
  obtain ⟨hM1, hMY, hMlog⟩ := floor_facts hY
  have hMlt := Nat.lt_floor_add_one (exp (5 * exp T))
  set M := ⌊exp (5 * exp T)⌋₊ with hMdef
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_exp] at hMlog
  have hlogM : log M ≤ 5 * exp T := by
    calc log M ≤ log (exp (5 * exp T)) := Real.log_le_log hM0 hMY
      _ = 5 * exp T := Real.log_exp _
  -- the start `n₀ = ⌈exp E⌉`
  have hn₀ge : exp E ≤ (⌈exp E⌉₊ : ℝ) := Nat.le_ceil _
  have hn₀lt : (⌈exp E⌉₊ : ℝ) < exp E + 1 := Nat.ceil_lt_add_one (exp_pos _).le
  set n₀ := ⌈exp E⌉₊ with hn₀def
  clear_value δ E M n₀
  have hexpE1 : 1 ≤ exp E := Real.one_le_exp (by linarith)
  have hn₀1' : (1 : ℝ) ≤ n₀ := le_trans hexpE1 hn₀ge
  have hn₀1 : 1 ≤ n₀ := by exact_mod_cast hn₀1'
  have hn₀M : n₀ ≤ M := by
    have h3 : exp E * exp 2 ≤ exp (5 * exp T) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
    have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos E).le
    have : (n₀ : ℝ) < M := by linarith
    exact_mod_cast this.le
  have hsplitM : ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖ ≤
      ‖∑ n ∈ Icc 1 n₀, χ n * (n : ℂ) ^ (-s)‖ + ‖∑ n ∈ Ioc n₀ M, χ n * (n : ℂ) ^ (-s)‖ := by
    have e1 : Icc 1 M = Ioc 0 M := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e2 : Icc 1 n₀ = Ioc 0 n₀ := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hn₀M]
    exact norm_add_le _ _
  -- the initial segment, trivially
  have hQ1 : ‖∑ n ∈ Icc 1 n₀, χ n * (n : ℂ) ^ (-s)‖ ≤ exp (11 * T ^ 2 + 1) := by
    refine (norm_sum_le_trivial χ n₀ s δ hδ0 hσ1).trans ?_
    have hlogn₀ : log n₀ ≤ E + 1 := by
      have h2 : (n₀ : ℝ) ≤ exp E * exp 1 := by
        have := mul_le_mul_of_nonneg_left he1 (exp_pos E).le
        linarith
      calc log n₀ ≤ log (exp E * exp 1) := Real.log_le_log (by linarith) h2
        _ = E + 1 := by rw [← exp_add, log_exp]
    have h1 : (n₀ : ℝ) ^ δ ≤ exp (10 * T ^ 2 + 1) :=
      (rpow_le_exp_of_log_le hn₀1' le_rfl hδ0 hlogn₀).trans (exp_le_exp.mpr hδE)
    have h2 : 1 + log n₀ ≤ exp (T ^ 2) := by
      have h3 : exp T ≤ exp (T ^ 2) := exp_le_exp.mpr hTT2
      linarith
    calc (n₀ : ℝ) ^ δ * (1 + log n₀) ≤ exp (10 * T ^ 2 + 1) * exp (T ^ 2) :=
          mul_le_mul h1 h2 (by linarith [Real.log_nonneg hn₀1']) (exp_pos _).le
      _ = exp (11 * T ^ 2 + 1) := by rw [← exp_add]; ring_nf
  -- the dyadic blocks
  set E₃ := exp T / T ^ C₃ with hE₃def
  clear_value E₃
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hblock : ∀ k ∈ range (Nat.log 2 M + 1),
      ‖∑ m ∈ Ioc (min (n₀ * 2 ^ k) M) (min (n₀ * 2 ^ (k + 1)) M), χ m * (m : ℂ) ^ (-s)‖ ≤
        |K₃| * exp (50 * T ^ 4) * exp (-E₃) := by
    intro k _
    have hRHS : 0 ≤ |K₃| * exp (50 * T ^ 4) * exp (-E₃) := by positivity
    have hmono : n₀ * 2 ^ k ≤ n₀ * 2 ^ (k + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    by_cases hk : M ≤ n₀ * 2 ^ k
    · rw [min_eq_right hk, min_eq_right (le_trans hk hmono), Finset.Ioc_self, Finset.sum_empty,
        norm_zero]
      exact hRHS
    · replace hk := not_le.mp hk
      rw [min_eq_left hk.le]
      have hA1 : 1 ≤ n₀ * 2 ^ k := le_trans hn₀1 (Nat.le_mul_of_pos_right _ (by positivity))
      have hAB : n₀ * 2 ^ k ≤ min (n₀ * 2 ^ (k + 1)) M := le_min hmono hk.le
      have hB : min (n₀ * 2 ^ (k + 1)) M ≤ 2 * (n₀ * 2 ^ k) := by
        have : n₀ * 2 ^ (k + 1) = 2 * (n₀ * 2 ^ k) := by rw [pow_succ]; ring
        omega
      have hAge : exp E ≤ ((n₀ * 2 ^ k : ℕ) : ℝ) :=
        le_trans hn₀ge (by exact_mod_cast Nat.le_mul_of_pos_right _ (by positivity))
      have hAM : ((n₀ * 2 ^ k : ℕ) : ℝ) ≤ M := by exact_mod_cast hk.le
      have hAle : ((n₀ * 2 ^ k : ℕ) : ℝ) ≤ 2 * exp (5 * exp T) := by
        linarith [exp_pos (5 * exp T)]
      have hb := block_bound (Nat.pos_of_ne_zero (NeZero.ne q)) χ s (by linarith) (n₀ * 2 ^ k) _
        hA1 hAB hB (K₃ * (((n₀ * 2 ^ k : ℕ) : ℝ) / q) * exp (-E₃))
        (fun a J hJ hJs => hLP _ hAge hAle a J hJ hJs)
      refine hb.trans ?_
      set A : ℝ := ((n₀ * 2 ^ k : ℕ) : ℝ) with hAdef
      have hA1' : (1 : ℝ) ≤ A := by rw [hAdef]; exact_mod_cast hA1
      have hA0 : (0 : ℝ) < A := by linarith
      have hApow : A * A ^ (-s.re) = A ^ (1 - s.re) := by
        rw [sub_eq_add_neg, Real.rpow_add hA0, Real.rpow_one]
      have hlogA : log A ≤ 5 * exp T := le_trans (Real.log_le_log hA0 hAM) hlogM
      have hAδ : A ^ (1 - s.re) ≤ exp (50 * T ^ 4) := by
        rw [← hδ5L]; exact rpow_le_exp_of_log_le hA1' hσ2 hδ0 hlogA
      have hApos : 0 ≤ A ^ (1 - s.re) := Real.rpow_nonneg hA0.le _
      calc (q : ℝ) * (K₃ * (A / q) * exp (-E₃)) * A ^ (-s.re)
          = K₃ * (A * A ^ (-s.re)) * exp (-E₃) := by field_simp
        _ = K₃ * A ^ (1 - s.re) * exp (-E₃) := by rw [hApow]
        _ ≤ |K₃| * A ^ (1 - s.re) * exp (-E₃) := by
            gcongr; exact le_abs_self _
        _ ≤ |K₃| * exp (50 * T ^ 4) * exp (-E₃) := by gcongr
  have hKb : ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ 11 * exp T := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 M) ≤ M := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : M ≠ 0)
    have hlog : (Nat.log 2 M : ℝ) * log 2 ≤ log M := by
      have := Real.log_le_log (by positivity) hpow
      rwa [Real.log_pow] at this
    have hl2 : (1 / 2 : ℝ) ≤ log 2 := by have := Real.log_two_gt_d9; linarith
    have h5 : (Nat.log 2 M : ℝ) * (1 / 2) ≤ (Nat.log 2 M : ℝ) * log 2 :=
      mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _)
    push_cast
    linarith
  have hQ2 : ‖∑ n ∈ Ioc n₀ M, χ n * (n : ℂ) ^ (-s)‖ ≤ 1 := by
    have hmin : min (n₀ * 2 ^ (Nat.log 2 M + 1)) M = M := by
      apply min_eq_right
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) M
      calc M ≤ 2 ^ (Nat.log 2 M + 1) := this.le
        _ ≤ n₀ * 2 ^ (Nat.log 2 M + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have hdy := sum_Ioc_dyadic (fun m => χ m * (m : ℂ) ^ (-s)) n₀ M hn₀M (Nat.log 2 M + 1)
    rw [hmin] at hdy
    rw [hdy]
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum hblock).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    have hc₀ : 0 ≤ log (11 * |K₃| + 1) := Real.log_nonneg (by linarith [abs_nonneg K₃])
    have hTn : T ^ C₃ ≤ T ^ n := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hn
    have hTpos : 0 < T ^ C₃ := Real.rpow_pos_of_pos hT0 _
    have hE₃ : log (11 * |K₃| + 1) + T + 50 * T ^ 4 ≤ E₃ := by
      rw [hE₃def, le_div_iff₀ hTpos]
      have hT14 : T ≤ T ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
      have h1 : log (11 * |K₃| + 1) + T + 50 * T ^ 4 ≤ (log (11 * |K₃| + 1) + 51) * T ^ 4 := by
        have h7 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ T ^ 4 by linarith) hc₀
        linarith only [h7, hT14, show (log (11 * |K₃| + 1) + 51) * T ^ 4 =
          log (11 * |K₃| + 1) * T ^ 4 + 51 * T ^ 4 by ring]
      have h2 : (log (11 * |K₃| + 1) + 51) * T ^ 4 * T ^ n ≤ exp T := by
        rw [mul_assoc, ← pow_add, add_comm 4 n]; exact hTb
      calc (log (11 * |K₃| + 1) + T + 50 * T ^ 4) * T ^ C₃
          ≤ (log (11 * |K₃| + 1) + 51) * T ^ 4 * T ^ n :=
            mul_le_mul h1 hTn hTpos.le (by positivity)
        _ ≤ exp T := h2
    have hexp : (11 * |K₃| + 1) * exp T * exp (50 * T ^ 4) * exp (-E₃) ≤ 1 := by
      have e : (11 * |K₃| + 1) * exp T * exp (50 * T ^ 4) * exp (-E₃) =
          exp (log (11 * |K₃| + 1) + T + 50 * T ^ 4 + -E₃) := by
        rw [exp_add, exp_add, exp_add, exp_log (by positivity)]
      rw [e]
      exact le_of_le_of_eq (exp_le_exp.mpr (by linarith only [hE₃])) exp_zero
    have hX : 0 ≤ |K₃| * exp (50 * T ^ 4) * exp (-E₃) := by positivity
    have := mul_le_mul_of_nonneg_right hKb hX
    have e2 : (11 * |K₃| + 1) * exp T * exp (50 * T ^ 4) * exp (-E₃) =
        11 * exp T * (|K₃| * exp (50 * T ^ 4) * exp (-E₃)) +
          exp T * exp (50 * T ^ 4) * exp (-E₃) := by ring
    have h8 : 0 ≤ exp T * exp (50 * T ^ 4) * exp (-E₃) := by positivity
    linarith only [this, e2, hexp, h8]
  -- the pole term
  have hQ3 : (M : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 1 := by
    have hn : exp (E / 2) < ‖s - 1‖ :=
      lt_of_lt_of_le hv1 (by simpa using Complex.abs_im_le_norm (s - 1))
    have h1 : (M : ℝ) ^ (1 - s.re) ≤ exp (50 * T ^ 4) := by
      rw [← hδ5L]; exact rpow_le_exp_of_log_le hM1' hσ2 hδ0 hlogM
    have h100 : 100 * T ^ 4 ≤ E := by
      rw [hEdef, le_div_iff₀ (by positivity)]
      have : 100 * T ^ 4 * T ^ 2 = 100 * T ^ 6 := by ring
      linarith
    have h2 : exp (50 * T ^ 4) ≤ exp (E / 2) := exp_le_exp.mpr (by linarith only [h100])
    rw [div_le_one (by linarith only [hn, exp_pos (E / 2)])]
    linarith only [h1, h2, hn]
  -- the remainder
  have hQ4 : ‖s‖ * ((2 * q + 1) * (M : ℝ) ^ (-s.re) / s.re) ≤ 1 := by
    have hs : ‖s‖ ≤ exp (3 * exp T + 2) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im s
      have h2 : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, hσ2'⟩
      have h3 : 1 ≤ exp (3 * exp T) := Real.one_le_exp (by linarith)
      have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos (3 * exp T)).le
      rw [exp_add]; linarith
    have hq' : 2 * (q : ℝ) + 1 ≤ exp (C * T + 2) := by
      have h3 : 1 ≤ exp (C * T) := Real.one_le_exp (by positivity)
      have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos (C * T)).le
      rw [exp_add]; linarith
    have hMs : (M : ℝ) ^ (-s.re) ≤ exp (-(4 / 5 * (5 * exp T - 1))) :=
      rpow_neg_le_exp hM0 hσ45 (by norm_num) hMlog (by linarith)
    refine (err_le hσ45 hM0.le hs hq' hMs).trans (le_of_le_of_eq (exp_le_exp.mpr ?_) exp_zero)
    have hT3 : T ≤ T ^ 3 := hTT3
    have h5 : (C + 6) * T ≤ (C + 6) * T ^ 3 := mul_le_mul_of_nonneg_left hT3 (by linarith)
    have h6 : C * T + 6 * T ≤ exp T := by linarith [show (C + 6) * T = C * T + 6 * T by ring]
    linarith
  -- assemble
  have him : s.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hv1; linarith [exp_pos (E / 2)]
  have hsub := norm_LFunction_sub_le χ M hM1 (s := s) (by linarith) him
  refine (norm_le_of_sub (S := ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s))).trans ?_
  have hfin : exp (11 * T ^ 2 + 1) + 3 ≤ exp (100 * T ^ 2) := by
    have h1 : 1 ≤ exp (11 * T ^ 2 + 1) := Real.one_le_exp (by positivity)
    have h3 : exp (11 * T ^ 2 + 1) * exp 2 ≤ exp (100 * T ^ 2) := by
      rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
    have h4 := mul_le_mul_of_nonneg_left he2 (exp_pos (11 * T ^ 2 + 1)).le
    linarith
  linarith only [hsplitM, hQ1, hQ2, hQ3, hQ4, hsub, hfin]

end ArtinPrimitiveRoots.L31L

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (C : ℝ) (hC : 0 < C) :
    ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ log x ^ C →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ v : ℝ,
        |σ - 1| ≤ 10 * (log (log x) ^ 4 / log x) → 1 / 2 ≤ |v| → |v| ≤ 3 * x ^ 3 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          exp (K * log (log x) ^ 2) := by
  obtain ⟨C₃, K₃, _hC₃, hLP⟩ := log_phase_progression
  obtain ⟨x₁, hx₁⟩ := hLP C hC
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈C₃⌉₊ := ⟨_, rfl⟩
  have hev : ∀ᶠ T in Filter.atTop, 2 ≤ T ∧ 50 * T ^ 4 ≤ exp T ∧ 100 * T ^ 6 ≤ exp T ∧
      (C + 6) * T ^ 3 ≤ exp T ∧ (log (11 * |K₃| + 1) + 51) * T ^ (n + 4) ≤ exp T :=
    (Filter.eventually_ge_atTop 2).and ((L31L.ev_pow_le_exp _ 4).and
      ((L31L.ev_pow_le_exp _ 6).and ((L31L.ev_pow_le_exp _ 3).and (L31L.ev_pow_le_exp _ _))))
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨100, max x₁ (exp (exp (max T₀ 2))), fun x hx q _ hq χ σ v hσ hv1 hv2 => ?_⟩
  have hx₁x : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : exp (exp (max T₀ 2)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hxe
  have hL : exp (max T₀ 2) ≤ log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hL0 : 0 < log x := lt_of_lt_of_le (exp_pos _) hL
  have hTge : max T₀ 2 ≤ log (log x) := by rw [Real.le_log_iff_exp_le hL0]; exact hL
  obtain ⟨G1, G2, G3, G4, G5⟩ := hT₀ (log (log x)) (le_trans (le_max_left _ _) hTge)
  have hx3 : x ^ 3 = exp (3 * log x) := by
    rw [show (3 : ℝ) * log x = ((3 : ℕ) : ℝ) * log x by norm_num, Real.exp_nat_mul, exp_log hx0]
  have hx5 : x ^ 5 = exp (5 * log x) := by
    rw [show (5 : ℝ) * log x = ((5 : ℕ) : ℝ) * log x by norm_num, Real.exp_nat_mul, exp_log hx0]
  have H := hx₁ x hx₁x
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set s : ℂ := (σ : ℂ) + (v : ℂ) * Complex.I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = v := by simp [hs]
  obtain ⟨T, hT⟩ : ∃ T, log (log x) = T := ⟨_, rfl⟩
  have hLe : log x = exp T := by rw [← hT, exp_log hL0]
  rw [hx3] at hv2
  rw [hT] at hσ ⊢
  rw [hLe] at hσ hq hv2
  rw [hT] at G1 G2 G3 G4 G5
  have hqT : (q : ℝ) ≤ exp (C * T) := by rwa [← Real.exp_mul, mul_comm] at hq
  rw [← hre] at hσ
  rw [← him] at hv1 hv2
  by_cases hcase : |s.im| ≤ exp (exp T / (2 * T ^ 2))
  · exact L31L.range_small C T hC G1 G2 G4 q hqT χ s hσ hv1 hcase
  · refine L31L.range_large C T C₃ K₃ n hC G1 G2 G3 G4 (hn ▸ Nat.le_ceil C₃) G5 q hqT χ s hσ
      (not_le.mp hcase) hv2 (fun N h1 h2 a J hJ hJN => ?_)
    have h := H N (by rw [hT, hLe]; exact h1) (by rw [hx5, hLe]; exact h2) q hq0 (by rw [hLe]; exact hq) (-s.im)
      (by rw [abs_neg, hT, hLe]; exact (not_le.mp hcase).le)
      (by rw [abs_neg, hx3, hLe]; linarith [exp_pos (3 * exp T)]) a J hJ hJN
    rw [hT, hLe] at h
    exact h
end
