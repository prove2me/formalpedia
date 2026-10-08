-- Prove2me | solution 1 for ArtinPrimitiveRoots.primitive_root_primes_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T08:59:19.789209+00:00
-- url     : https://prove2.me/submissions/6e8fa316-b000-4e15-acd7-65feeed36970
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_controlled_predecessors
import Theorems.Thm_ArtinPrimitiveRoots_uniform_splitting_bound
import Theorems.Thm_ArtinPrimitiveRoots_exists_quadratic_nonresidue_progression

open Filter Asymptotics

namespace ArtinPrimitiveRoots.Thm11

/-- The `ncard` of a finite indexed union is at most the sum of the `ncard`s. -/
lemma ncard_biUnion_le {ι : Type*} (s : Finset ι) (T : ι → Set ℕ) :
    (⋃ i ∈ s, T i).ncard ≤ ∑ i ∈ s, (T i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- `B a J = ∏_{1 ≤ j ≤ J} |a^j - 1|`. -/
def B (a : ℤ) (J : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 J, (a ^ j - 1).natAbs

lemma B_ne_zero {a : ℤ} (ha : 1 < |a|) (J : ℕ) : B a J ≠ 0 := by
  unfold B
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [Int.natAbs_ne_zero, sub_ne_zero]
  intro h
  have h1 : |a ^ j| = 1 := by rw [h]; simp
  rw [abs_pow] at h1
  have : 1 < |a| ^ j := one_lt_pow₀ ha (by omega)
  linarith

lemma B_le {a : ℤ} (ha : 1 < |a|) (J : ℕ) : B a J ≤ a.natAbs ^ (2 * J * J) := by
  have hA : 2 ≤ a.natAbs := by
    have : (1:ℤ) < (a.natAbs : ℤ) := by rwa [Int.natCast_natAbs]
    omega
  unfold B
  calc ∏ j ∈ Finset.Icc 1 J, (a ^ j - 1).natAbs
      ≤ (a.natAbs ^ (2 * J)) ^ (Finset.Icc 1 J).card := by
        apply Finset.prod_le_pow_card
        intro j hj
        obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.mp hj
        calc (a ^ j - 1).natAbs ≤ (a ^ j).natAbs + (1:ℤ).natAbs := Int.natAbs_sub_le _ _
          _ = a.natAbs ^ j + 1 := by rw [Int.natAbs_pow]; rfl
          _ ≤ a.natAbs ^ (j + 1) := by
            rw [pow_succ]
            have : 1 ≤ a.natAbs ^ j := Nat.one_le_pow _ _ (by omega)
            nlinarith
          _ ≤ a.natAbs ^ (2 * J) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = a.natAbs ^ (2 * J * J) := by rw [Nat.card_Icc, ← pow_mul]; congr 1

lemma card_large_primeFactors_mul_log_le (n : ℕ) (hn : n ≠ 0) (x : ℝ) (hx : 0 < x) :
    ((n.primeFactors.filter (fun p : ℕ => x < (p : ℝ))).card : ℝ) * Real.log x ≤ Real.log n := by
  set F := n.primeFactors.filter (fun p : ℕ => x < (p : ℝ))
  have h1 : ∏ p ∈ F, p ∣ n :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  have h2 : (∏ p ∈ F, p : ℕ) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
  have h3 : x ^ F.card ≤ ∏ p ∈ F, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hx.le) (fun p hp => (Finset.mem_filter.mp hp).2.le)
  have h4 : x ^ F.card ≤ (n : ℝ) := h3.trans (by rw [← Nat.cast_prod]; exact Nat.cast_le.mpr h2)
  rw [← Real.log_pow]
  exact Real.log_le_log (pow_pos hx _) h4

lemma sum_inv_mul_pred_Ico_eq (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : k ≤ n) :
    ∑ m ∈ Finset.Ico k n, 1 / ((m : ℝ) * ((m : ℝ) - 1)) = 1 / ((k : ℝ) - 1) - 1 / ((n : ℝ) - 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [Finset.sum_Ico_succ_top hkn, ih]
    have h1 : (2:ℝ) ≤ n := by exact_mod_cast hk.trans hkn
    have h2 : (n:ℝ) - 1 ≠ 0 := by linarith
    have h3 : (n:ℝ) ≠ 0 := by linarith
    have h4 : (k:ℝ) - 1 ≠ 0 := by
      have : (2:ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [show ((n + 1 : ℕ) : ℝ) - 1 = n by push_cast; ring]
    field_simp
    ring

lemma sum_inv_mul_pred_Ico_le (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    ∑ m ∈ Finset.Ico k n, 1 / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 / ((k : ℝ) - 1) := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  rcases le_or_gt k n with h | h
  · rw [sum_inv_mul_pred_Ico_eq k hk n h]
    have : (k:ℝ) ≤ n := by exact_mod_cast h
    have : 0 ≤ 1 / ((n:ℝ) - 1) := by apply div_nonneg <;> linarith
    linarith
  · rw [Finset.Ico_eq_empty_of_le h.le, Finset.sum_empty]
    apply div_nonneg <;> linarith

/-- The algebraic core: an odd prime `p` with `(a/p) = -1` and `p - 1 = c r Q`, at which `a`
is not a primitive root, has `a^((p-1)/Q) = 1` or `a^((p-1)/q) = 1` for a prime `q ∣ r`. -/
lemma key (a : ℤ) (p c r Q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpa : ¬ (p : ℤ) ∣ a)
    (hleg : @legendreSym p ⟨hp⟩ a = -1) (hc : c = 2 ∨ c = 4) (hpc : p - 1 = c * r * Q)
    (hQ : Q.Prime) (hr : 0 < r) (hord : orderOf (a : ZMod p) ≠ p - 1) :
    (a : ZMod p) ^ ((p - 1) / Q) = 1 ∨
      ∃ q ∈ r.primeFactors, (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  have := Fact.mk hp
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have hg0 : (a : ZMod p) ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).not.mpr hpa
  have hpow : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hg0
  have heul : (a : ZMod p) ^ (p / 2) = -1 := by
    have := legendreSym.eq_pow p a
    rw [hleg] at this
    push_cast at this
    exact this.symm
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  obtain ⟨i, hi⟩ := orderOf_dvd_of_pow_eq_one hpow
  have hi1 : i ≠ 1 := by
    rintro rfl
    exact hord (by rw [hi, mul_one])
  obtain ⟨q, hq, hqi⟩ := Nat.exists_prime_and_dvd hi1
  obtain ⟨k, hk⟩ := hqi
  have hdiv : (p - 1) / q = orderOf (a : ZMod p) * k := by
    rw [hi, hk, show orderOf (a : ZMod p) * (q * k) = orderOf (a : ZMod p) * k * q by ring]
    exact Nat.mul_div_cancel _ hq.pos
  have hgq : (a : ZMod p) ^ ((p - 1) / q) = 1 := by
    rw [hdiv, pow_mul, pow_orderOf_eq_one, one_pow]
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : p / 2 = (p - 1) / 2 := by omega
    rw [this, hgq] at heul
    exact ZMod.neg_one_ne_one heul.symm
  have hqp : q ∣ c * r * Q := by
    rw [← hpc, hi, hk]
    exact ⟨orderOf (a : ZMod p) * k, by ring⟩
  rcases (Nat.Prime.dvd_mul hq).mp hqp with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
    · exfalso
      have h2 : q ∣ 2 := by
        rcases hc with rfl | rfl
        · exact h'
        · exact hq.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by simpa using h')
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
    · exact Or.inr ⟨q, Nat.mem_primeFactors.mpr ⟨hq, h', hr.ne'⟩, hgq⟩
  · left
    rw [← (Nat.prime_dvd_prime_iff_eq hq hQ).mp h]
    exact hgq

lemma E1_bound (a : ℤ) (hA : 1 < |a|) (C x : ℝ) (hxpos : 0 < x) (hL0 : 0 < Real.log x)
    (c2 : 32 * Real.log a.natAbs * Real.log x ≤ C * x ^ (0.8:ℝ)) :
    (((B a ⌊2 * x ^ (0.1:ℝ)⌋₊).primeFactors.filter (fun p : ℕ => x < (p : ℝ))).card : ℝ) *
      Real.log x ^ 2 ≤ C * x / 4 := by
  set J := ⌊2 * x ^ (0.1:ℝ)⌋₊ with hJ
  set e := (((B a J).primeFactors.filter (fun p : ℕ => x < (p : ℝ))).card : ℝ) with he
  set L := Real.log x with hL
  set l := Real.log a.natAbs with hl
  set y := x ^ (0.2:ℝ) with hy
  have h1 : e * L ≤ Real.log (B a J) :=
    card_large_primeFactors_mul_log_le (B a J) (B_ne_zero hA J) x hxpos
  have hBpos : (0:ℝ) < (B a J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (B_ne_zero hA J)
  have hBle : Real.log (B a J) ≤ ((2 * J * J : ℕ) : ℝ) * l := by
    rw [← Real.log_pow]
    apply Real.log_le_log hBpos
    exact_mod_cast B_le hA J
  have hJx : (J:ℝ) ≤ 2 * x ^ (0.1:ℝ) := Nat.floor_le (by positivity)
  have hJ0 : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hxx : x ^ (0.1:ℝ) * x ^ (0.1:ℝ) = y := by
    rw [hy, ← Real.rpow_add hxpos]; norm_num
  have hxx' : y * x ^ (0.8:ℝ) = x := by
    rw [hy, ← Real.rpow_add hxpos]; norm_num
  have hlogA : 0 ≤ l := Real.log_natCast_nonneg _
  have hJJ : (J:ℝ) * J ≤ 4 * y := by
    have := mul_le_mul hJx hJx hJ0 (by positivity)
    linarith
  push_cast at hBle
  have hJJl : (J:ℝ) * J * l ≤ 4 * y * l := mul_le_mul_of_nonneg_right hJJ hlogA
  have h2 : e * L ≤ 8 * y * l := by linarith
  have hy0 : 0 ≤ y := by positivity
  have h3 : e * L ^ 2 ≤ 8 * y * l * L := by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 hL0.le
  have h4 : y * (32 * l * L) ≤ y * (C * x ^ (0.8:ℝ)) :=
    mul_le_mul_of_nonneg_left c2 hy0
  have h5 : y * (C * x ^ (0.8:ℝ)) = C * x := by
    rw [show y * (C * x ^ (0.8:ℝ)) = C * (y * x ^ (0.8:ℝ)) by ring, hxx']
  linarith

lemma final_arith (C C₂ x L Y Z δ xp g e s : ℝ) (hC : 0 < C) (_hC₂ : 0 ≤ C₂) (hxpos : 0 < x)
    (hL0 : 0 < L) (hYpos : 0 < Y) (hZ0 : 0 ≤ Z) (hxeq : x = Real.exp L)
    (c4 : 16 * C₂ * L ≤ C * Y) (hZe : Z ≤ Real.exp (δ * L / 2))
    (c6 : 16 * C₂ * L ^ 2 ≤ C * Real.exp (δ * L / 2)) (hx1δ : xp = Real.exp (L * (1 - δ)))
    (htot : C * x / L ^ 2 ≤ g + e + s) (hE1 : e * L ^ 2 ≤ C * x / 4)
    (hsumT : s ≤ C₂ * x / L * (2 / Y) + 2 * Z * (C₂ * xp)) :
    C / 2 * x / L ^ 2 ≤ g := by
  have hT1 : C₂ * x / L * (2 / Y) * L ^ 2 ≤ C * x / 8 := by
    rw [show C₂ * x / L * (2 / Y) * L ^ 2 = (16 * C₂ * L) * x / (8 * Y) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_right c4 (by positivity : (0:ℝ) ≤ 8 * x)
    linarith
  have hxp0 : 0 ≤ xp := by rw [hx1δ]; positivity
  have hT2 : 2 * Z * (C₂ * xp) * L ^ 2 ≤ C * x / 8 := by
    calc 2 * Z * (C₂ * xp) * L ^ 2 = (16 * C₂ * L ^ 2) * (Z * xp) / 8 := by
          ring
      _ ≤ (C * Real.exp (δ * L / 2)) * (Real.exp (δ * L / 2) * Real.exp (L * (1 - δ))) / 8 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          apply mul_le_mul c6 (mul_le_mul hZe hx1δ.le hxp0 (by positivity))
            (by positivity) (by positivity)
      _ = C * x / 8 := by
          rw [hxeq, mul_assoc C, ← Real.exp_add, ← Real.exp_add,
            show δ * L / 2 + (δ * L / 2 + L * (1 - δ)) = L by ring]
  have hL2 : 0 < L ^ 2 := by positivity
  rw [div_le_iff₀ hL2] at htot ⊢
  have hs2 := mul_le_mul_of_nonneg_right hsumT hL2.le
  have : (g + e + s) * L ^ 2 = g * L ^ 2 + e * L ^ 2 + s * L ^ 2 := by ring
  have : (C₂ * x / L * (2 / Y) + 2 * Z * (C₂ * xp)) * L ^ 2 =
      C₂ * x / L * (2 / Y) * L ^ 2 + 2 * Z * (C₂ * xp) * L ^ 2 := by ring
  linarith

lemma ev_le_of_isLittleO {f g : ℝ → ℝ} (h : f =o[atTop] g) (K C : ℝ) (hC : 0 < C) :
    ∀ᶠ y in atTop, K * ‖f y‖ ≤ C * ‖g y‖ := by
  have hK : 0 < |K| + 1 := by positivity
  filter_upwards [h.def (c := C / (|K| + 1)) (by positivity)] with y hy
  calc K * ‖f y‖ ≤ (|K| + 1) * ‖f y‖ := by nlinarith [le_abs_self K, norm_nonneg (f y)]
    _ ≤ (|K| + 1) * (C / (|K| + 1) * ‖g y‖) := by gcongr
    _ = C * ‖g y‖ := by field_simp

lemma asymp (C C₂ K : ℝ) (hC : 0 < C) (q₀ : ℕ) : ∀ᶠ x : ℝ in atTop,
    3 ≤ x ∧ K * Real.log x ≤ C * x ^ (0.8:ℝ) ∧
    max 2 (q₀:ℝ) ≤ Real.exp (Real.log x ^ (0.1:ℝ)) ∧
    16 * C₂ * Real.log x ≤ C * Real.exp (Real.log x ^ (0.1:ℝ)) ∧
    Real.log x ^ (0.3:ℝ) ≤ (1 / 10 ^ 6 : ℝ) * Real.log x / 2 ∧
    16 * C₂ * Real.log x ^ 2 ≤ C * Real.exp ((1 / 10 ^ 6 : ℝ) * Real.log x / 2) := by
  have hlog := Real.tendsto_log_atTop
  -- (2)
  have h2 : ∀ᶠ x : ℝ in atTop, K * Real.log x ≤ C * x ^ (0.8:ℝ) := by
    filter_upwards [ev_le_of_isLittleO (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 0.8))
      K C hC, eventually_ge_atTop 1] with x hx hx1
    rwa [Real.norm_of_nonneg (Real.log_nonneg hx1),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  -- (3)
  have hY : Tendsto (fun x : ℝ => Real.exp (Real.log x ^ (0.1:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 0.1)).comp hlog)
  have h3 := hY.eventually_ge_atTop (max 2 (q₀:ℝ))
  -- (4)
  have h4L : ∀ᶠ L : ℝ in atTop, 16 * C₂ * L ≤ C * Real.exp (L ^ (0.1:ℝ)) := by
    have := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 0.1)).eventually
      (ev_le_of_isLittleO (isLittleO_pow_exp_pos_mul_atTop 10 one_pos) (16 * C₂) C hC)
    filter_upwards [this, eventually_ge_atTop 0] with L hL hL0
    have he : (L ^ (0.1:ℝ)) ^ (10:ℕ) = L := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
    simp only [he, one_mul] at hL
    rwa [Real.norm_of_nonneg hL0, Real.norm_of_nonneg (Real.exp_pos _).le] at hL
  have h4 := hlog.eventually h4L
  -- (5)
  have h5L : ∀ᶠ L : ℝ in atTop, L ^ (0.3:ℝ) ≤ (1 / 10 ^ 6 : ℝ) * L / 2 := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ) < 0.7)).eventually_ge_atTop
      (2 * 10 ^ 6), eventually_gt_atTop 0] with L hL hL0
    have he : L = L ^ (0.3:ℝ) * L ^ (0.7:ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hp : 0 ≤ L ^ (0.3:ℝ) := Real.rpow_nonneg hL0.le _
    have : L ^ (0.3:ℝ) * (2 * 10 ^ 6) ≤ L ^ (0.3:ℝ) * L ^ (0.7:ℝ) :=
      mul_le_mul_of_nonneg_left hL hp
    linarith
  have h5 := hlog.eventually h5L
  -- (6)
  have h6L : ∀ᶠ L : ℝ in atTop,
      16 * C₂ * L ^ 2 ≤ C * Real.exp ((1 / 10 ^ 6 : ℝ) * L / 2) := by
    filter_upwards [ev_le_of_isLittleO
      (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0:ℝ) < 1 / 10 ^ 6 / 2)) (16 * C₂) C hC,
      eventually_ge_atTop 0] with L hL hL0
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hL
    convert hL using 3
    · ring
  have h6 := hlog.eventually h6L
  filter_upwards [eventually_ge_atTop 3, h2, h3, h4, h5, h6] with x a1 a2 a3 a4 a5 a6
  exact ⟨a1, a2, a3, a4, a5, a6⟩

end ArtinPrimitiveRoots.Thm11

theorem solution (a : ℤ) (ha : a ≠ -1) (hsq : ¬ IsSquare a) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ^ 2 ≤
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
          orderOf (a : ZMod p) = p - 1} : ℝ) := by
  classical
  have ha0 : a ≠ 0 := fun h => hsq ⟨0, by simp [h]⟩
  have ha1 : a ≠ 1 := fun h => hsq ⟨1, by simp [h]⟩
  have hA : 1 < |a| := by
    rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  obtain ⟨c, hc, u, hu, hcu, hcop, hprog⟩ :=
    ArtinPrimitiveRoots.exists_quadratic_nonresidue_progression a ha hsq
  set M : ℕ := 8 * ∏ ℓ ∈ a.natAbs.primeFactors.filter (· ≠ 2), ℓ with hMdef
  have hMpos : 0 < M := by
    apply Nat.mul_pos (by norm_num)
    exact Finset.prod_pos (fun ℓ hℓ =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hℓ).1).pos)
  obtain ⟨C, hC, x₁, hS⟩ := ArtinPrimitiveRoots.controlled_predecessors M c u hMpos
    (dvd_mul_right 8 _) hc hu hcu hcop
  obtain ⟨⟨C₂, hC₂, q₀, x₂, hT⟩, -⟩ := ArtinPrimitiveRoots.uniform_splitting_bound a hA
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp
    (ArtinPrimitiveRoots.Thm11.asymp C C₂ (32 * Real.log a.natAbs) hC q₀)
  refine ⟨C / 2, by positivity, max (max x₁ x₂) (max x₃ 2),
    le_max_of_le_right (le_max_right _ _), ?_⟩
  intro x hx
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx2 : x₂ ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x₃ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨c3, c2, cY, c4, c5, c6⟩ := hx₃ x hx3
  have hSx := hS x hx1
  have hxpos : 0 < x := by linarith
  have hxeq : x = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
  set L := Real.log x with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set δ : ℝ := 1 / 10 ^ 6 with hδ
  set Y := Real.exp (L ^ (0.1:ℝ)) with hY
  set Z := Real.exp (L ^ (0.3:ℝ)) with hZ
  have hZx : Z ≤ x := by
    have : δ * L / 2 ≤ L := by rw [hδ]; nlinarith
    calc Z ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      _ = x := hxeq.symm
  have hY2 : 2 ≤ Y := le_trans (le_max_left _ _) cY
  set J := ⌊2 * x ^ (0.1:ℝ)⌋₊ with hJ
  set E1 : Finset ℕ := (ArtinPrimitiveRoots.Thm11.B a J).primeFactors.filter
    (fun p : ℕ => x < (p : ℝ)) with hE1
  set Qs : Finset ℕ := (Finset.Ico (⌊Y⌋₊ + 1) (⌊Z⌋₊ + 1)).filter Nat.Prime with hQs
  set T : ℕ → Set ℕ := fun q => {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧
    ¬ (p : ℤ) ∣ a * q ∧ p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} with hTdef
  set G := {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
    orderOf (a : ZMod p) = p - 1} with hG
  have hsub : {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
      ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
        ∀ ℓ ∈ r.primeFactors, Y < ℓ ∧ (ℓ : ℝ) < Z} ⊆ G ∪ ↑E1 ∪ ⋃ q ∈ Qs, T q := by
    intro p hp
    obtain ⟨hpp, hxp, hp2x, hpu, r, Q, hpc, hQ, hQx, hr, hℓ⟩ := hp
    obtain ⟨hpa, hleg⟩ := hprog p hpp hpu
    have hp2 : p ≠ 2 := by
      rintro rfl
      push_cast at hxp
      linarith
    by_cases hord : orderOf (a : ZMod p) = p - 1
    · exact Or.inl (Or.inl ⟨hpp, hxp, hp2x, hpa, hord⟩)
    rcases ArtinPrimitiveRoots.Thm11.key a p c r Q hpp hp2 hpa hleg hc hpc hQ hr hord with
      h | ⟨q, hq, h⟩
    · refine Or.inl (Or.inr ?_)
      have hj : (p - 1) / Q = c * r := by rw [hpc]; exact Nat.mul_div_cancel _ hQ.pos
      rw [hj] at h
      have hc2 : 2 ≤ c := by rcases hc with rfl | rfl <;> norm_num
      have hjpos : 1 ≤ c * r := by nlinarith
      have hjJ : c * r ≤ J := by
        apply Nat.le_floor
        have hx9 : 0 < x ^ (0.9:ℝ) := Real.rpow_pos_of_pos hxpos _
        have hxx : x ^ (0.1:ℝ) * x ^ (0.9:ℝ) = x := by
          rw [← Real.rpow_add hxpos]; norm_num
        have h1 : ((c * r : ℕ) : ℝ) * (Q : ℝ) + 1 = p := by
          have hp1 := hpp.two_le
          have : c * r * Q + 1 = p := by
            generalize c * r * Q = m at hpc ⊢
            omega
          exact_mod_cast this
        have hcr : (1:ℝ) ≤ ((c * r : ℕ) : ℝ) := by exact_mod_cast hjpos
        by_contra hcon
        push Not at hcon
        have e1 : 2 * x ^ (0.1:ℝ) * x ^ (0.9:ℝ) ≤ ((c * r : ℕ) : ℝ) * x ^ (0.9:ℝ) :=
          mul_le_mul_of_nonneg_right hcon.le hx9.le
        have e2 : ((c * r : ℕ) : ℝ) * x ^ (0.9:ℝ) < ((c * r : ℕ) : ℝ) * Q :=
          mul_lt_mul_of_pos_left hQx (by linarith)
        nlinarith
      have hdvd : p ∣ (a ^ (c * r) - 1).natAbs := by
        apply Int.natCast_dvd.mp
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
        push_cast
        rw [h, sub_self]
      have hB : (a ^ (c * r) - 1).natAbs ∣ ArtinPrimitiveRoots.Thm11.B a J :=
        Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hjpos, hjJ⟩)
      rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hpp, hdvd.trans hB, ArtinPrimitiveRoots.Thm11.B_ne_zero hA J⟩, hxp⟩
    · refine Or.inr ?_
      obtain ⟨hqY, hqZ⟩ := hℓ q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqr : q ∣ r := Nat.dvd_of_mem_primeFactors hq
      refine Set.mem_iUnion₂.mpr ⟨q, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨Nat.succ_le_of_lt ((Nat.floor_lt (Real.exp_pos _).le).mpr hqY),
          Nat.lt_succ_of_le (Nat.le_floor hqZ.le)⟩, hqp⟩
      · refine ⟨hpp, hxp, hp2x.le, ?_, ?_, h⟩
        · intro hdiv
          rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd hdiv with h' | h'
          · exact hpa h'
          · have h3 := Nat.le_of_dvd hqp.pos (Int.natCast_dvd_natCast.mp h')
            have h4 : (p:ℝ) ≤ q := by exact_mod_cast h3
            linarith
        · have hq1 : q ∣ p - 1 := by
            rw [hpc]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hqr c) Q
          exact ((Nat.modEq_iff_dvd' hpp.one_lt.le).mpr hq1).symm
  have hfin : (G ∪ ↑E1 ∪ ⋃ q ∈ Qs, T q).Finite := by
    refine (((Set.finite_Iio (⌊2 * x⌋₊ + 1)).subset ?_).union E1.finite_toSet).union ?_
    · exact fun p hp => Nat.lt_succ_of_le (Nat.le_floor hp.2.2.1.le)
    · exact Set.Finite.biUnion Qs.finite_toSet (fun q _ => (Set.finite_Iio (⌊2 * x⌋₊ + 1)).subset
        (fun p hp => Nat.lt_succ_of_le (Nat.le_floor hp.2.2.1)))
  have hcount : (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
      ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
        ∀ ℓ ∈ r.primeFactors, Y < ℓ ∧ (ℓ : ℝ) < Z} : ℝ) ≤
      G.ncard + E1.card + ∑ q ∈ Qs, ((T q).ncard : ℝ) := by
    rw [Nat.card_coe_set_eq]
    have := (Set.ncard_le_ncard hsub hfin).trans ((Set.ncard_union_le _ _).trans
      (Nat.add_le_add (Set.ncard_union_le _ _) (ArtinPrimitiveRoots.Thm11.ncard_biUnion_le Qs T)))
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  -- bound for E1
  have hE1 : (E1.card : ℝ) * L ^ 2 ≤ C * x / 4 :=
    ArtinPrimitiveRoots.Thm11.E1_bound a hA C x hxpos hL0 c2
  -- bound for each T q
  have hTq : ∀ q ∈ Qs, ((T q).ncard : ℝ) ≤
      C₂ * (x / (q * (q - 1) * L) + x ^ (1 - δ)) := by
    intro q hq
    obtain ⟨hqI, hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_Ico.mp hqI
    have hqY : Y < q := Nat.lt_of_floor_lt (Nat.lt_of_succ_le hq1)
    have hqZ : (q : ℝ) ≤ Z :=
      le_trans (Nat.cast_le.mpr (Nat.le_of_lt_succ hq2)) (Nat.floor_le (Real.exp_pos _).le)
    have hq0 : q₀ ≤ q := by
      have : (q₀ : ℝ) < q := lt_of_le_of_lt ((le_max_right _ _).trans cY) hqY
      exact_mod_cast this.le
    rw [← Nat.card_coe_set_eq]
    exact hT x hx2 q hqp hq0 hqZ
  have hsum1 : ∑ q ∈ Qs, 1 / ((q:ℝ) * ((q:ℝ) - 1)) ≤ 2 / Y := by
    have hk : 2 ≤ ⌊Y⌋₊ + 1 := by
      have : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    calc ∑ q ∈ Qs, 1 / ((q:ℝ) * ((q:ℝ) - 1))
        ≤ ∑ q ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊Z⌋₊ + 1), 1 / ((q:ℝ) * ((q:ℝ) - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m hm _
          have : (2:ℝ) ≤ m := by exact_mod_cast hk.trans (Finset.mem_Ico.mp hm).1
          apply div_nonneg zero_le_one
          nlinarith
      _ ≤ 1 / (((⌊Y⌋₊ + 1 : ℕ) : ℝ) - 1) :=
          ArtinPrimitiveRoots.Thm11.sum_inv_mul_pred_Ico_le _ hk _
      _ ≤ 2 / Y := by
          push_cast
          have hfl : Y - 1 < (⌊Y⌋₊ : ℝ) := by
            have := Nat.lt_floor_add_one Y
            linarith
          rw [add_sub_cancel_right, div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
  have hcardQs : (Qs.card : ℝ) ≤ 2 * Z := by
    have h1 : Qs.card ≤ ⌊Z⌋₊ + 1 := (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ico]; omega)
    have h2 : ((⌊Z⌋₊ : ℕ) : ℝ) ≤ Z := Nat.floor_le (Real.exp_pos _).le
    have h3 : 1 ≤ Z := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
    have : (Qs.card : ℝ) ≤ (⌊Z⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hsumT : ∑ q ∈ Qs, ((T q).ncard : ℝ) ≤
      C₂ * x / L * (2 / Y) + 2 * Z * (C₂ * x ^ (1 - δ)) := by
    calc ∑ q ∈ Qs, ((T q).ncard : ℝ)
        ≤ ∑ q ∈ Qs, C₂ * (x / (q * (q - 1) * L) + x ^ (1 - δ)) := Finset.sum_le_sum hTq
      _ = ∑ q ∈ Qs, (C₂ * x / L * (1 / ((q:ℝ) * ((q:ℝ) - 1))) + C₂ * x ^ (1 - δ)) :=
          Finset.sum_congr rfl (fun q _ => by
            rw [show x / ((q:ℝ) * (q - 1) * L) = x / L * (1 / ((q:ℝ) * (q - 1))) by
              rw [div_mul_div_comm, mul_one, mul_comm L]]
            ring)
      _ = C₂ * x / L * ∑ q ∈ Qs, 1 / ((q:ℝ) * ((q:ℝ) - 1)) + Qs.card * (C₂ * x ^ (1 - δ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ C₂ * x / L * (2 / Y) + 2 * Z * (C₂ * x ^ (1 - δ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hsum1 (by positivity)
          · exact mul_le_mul_of_nonneg_right hcardQs (by positivity)
  rw [Nat.card_coe_set_eq]
  exact ArtinPrimitiveRoots.Thm11.final_arith C C₂ x L Y Z δ (x ^ (1 - δ)) _ _ _ hC hC₂.le hxpos
    hL0 (Real.exp_pos _) (Real.exp_pos _).le hxeq c4 (Real.exp_le_exp.mpr c5) c6
    (Real.rpow_def_of_pos hxpos _) (hSx.trans hcount) hE1 hsumT
