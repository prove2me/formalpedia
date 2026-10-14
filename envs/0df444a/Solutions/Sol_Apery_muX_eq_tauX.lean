-- Prove2me | solution 1 for Apery.muX_eq_tauX
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T19:34:28.94099+00:00
-- url     : https://prove2.me/submissions/f10268b4-bedf-4605-aa46-1fed61b6d04a

/-
# The pullback identity `μ_X(P/D_K) = τ_X(pull K P)` (source `Apery/Arith/Pullback.lean`)

For every `K` and `P ∈ ℚ[X]`, the functional `μ_X` evaluated on the rational function
`P / D_K` equals the functional `τ_X` applied to the pullback `(-1)^K x⁵ P(-x²)` with the
simple integer pole set `±1, …, ±K`. The file ports the binomial basis and the Bernoulli
functional `Lb`, the polynomial part and residues of `PolarFun`, and the whole of
`Apery/Arith/Pullback.lean` (`pull`, the cofactors `B_j`, `piPl_PlK`, `polyPart_pull`,
`resP_pull`, `μX_eq_tauX`). Faithful port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Polynomial Matrix Finset

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

lemma poly_eq_of_nat {P Q : ℚ[X]} (h : ∀ n : ℕ, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℚ)) Nat.cast_injective
  intro n
  exact h n

/-! ### The Bernoulli functional -/

lemma Lb_add (P Q : ℚ[X]) : Lb (P + Q) = Lb P + Lb Q := by
  unfold Lb
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma Lb_smul (c : ℚ) (Q : ℚ[X]) : Lb (c • Q) = c * Lb Q := by
  unfold Lb
  rw [Polynomial.sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum, Polynomial.sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma Lb_C_mul (c : ℚ) (Q : ℚ[X]) : Lb (C c * Q) = c * Lb Q := by
  rw [← smul_eq_C_mul, Lb_smul]

lemma Lb_monomial (n : ℕ) (a : ℚ) : Lb (monomial n a) = a * _root_.bernoulli n := by
  unfold Lb
  rw [Polynomial.sum_monomial_index _ _ (by simp)]

lemma Lb_X_pow (n : ℕ) : Lb (X ^ n) = _root_.bernoulli n := by
  rw [← monomial_one_right_eq_X_pow, Lb_monomial, one_mul]

lemma Lb_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) : Lb (∑ i ∈ s, f i) = ∑ i ∈ s, Lb (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lb_add, ih]

lemma Lb_neg (Q : ℚ[X]) : Lb (-Q) = -Lb Q := by
  rw [show -Q = (-1 : ℚ) • Q by simp, Lb_smul]; ring

lemma Lb_sub (P Q : ℚ[X]) : Lb (P - Q) = Lb P - Lb Q := by
  rw [sub_eq_add_neg, Lb_add, Lb_neg, sub_eq_add_neg]

/-- **Shift identity**: `Lb (Q(x+1)) - Lb Q = Q'(0)`. -/
theorem Lb_shift (Q : ℚ[X]) : Lb (Q.comp (X + 1)) - Lb Q = Q.derivative.eval 0 := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, Lb_add, Lb_add, derivative_add, eval_add, ← hP, ← hQ]; ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Lb_C_mul, Lb_C_mul, Lb_X_pow,
      derivative_C_mul_X_pow, eval_C_mul, eval_pow, eval_X]
    rw [add_pow, Lb_sum]
    simp only [one_pow, mul_one]
    have e : ∀ k ∈ range (n + 1), Lb (X ^ k * (n.choose k : ℚ[X])) = (n.choose k : ℚ) * _root_.bernoulli k := by
      intro k _
      rw [show (X ^ k * (n.choose k : ℚ[X])) = C (n.choose k : ℚ) * X ^ k by
        rw [mul_comm]; simp, Lb_C_mul, Lb_X_pow]
    rw [Finset.sum_congr rfl e, Finset.sum_range_succ, _root_.sum_bernoulli, Nat.choose_self]
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp; ring
      · simp

/-! ### The binomial basis -/

lemma bin_eval_nat (k m : ℕ) : (bin k).eval (m : ℚ) = (m.choose k : ℚ) := by
  unfold bin
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

lemma bin_zero : bin 0 = 1 := by simp [bin]

lemma bin_eval_zero {k : ℕ} (hk : 1 ≤ k) : (bin k).eval 0 = 0 := by
  have := bin_eval_nat k 0
  simp only [Nat.cast_zero] at this
  rw [this, Nat.choose_eq_zero_of_lt hk]; simp

/-- **Pascal**: `bin (k+1) (x+1) = bin (k+1) x + bin k x`. -/
lemma bin_comp_add_one (k : ℕ) : (bin (k + 1)).comp (X + 1) = bin (k + 1) + bin k := by
  apply poly_eq_of_nat
  intro m
  rw [eval_comp, eval_add, eval_X, eval_one, eval_add, show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by
    push_cast; ring, bin_eval_nat, bin_eval_nat, bin_eval_nat, Nat.choose_succ_succ']
  push_cast; ring

lemma descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1) ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, eval_mul, ih, eval_sub, eval_X, eval_natCast,
      Nat.factorial_succ]
    push_cast; ring

/-- `bin_k'(0) = (-1)^{k-1}/k`. -/
lemma bin_derivative_eval_zero (k : ℕ) :
    (bin (k + 1)).derivative.eval 0 = (-1) ^ k / (k + 1 : ℚ) := by
  unfold bin
  rw [derivative_C_mul, eval_mul, eval_C, descPochhammer_succ_left, derivative_mul, derivative_X,
    one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero, eval_comp, eval_sub, eval_X,
    eval_one, zero_sub, descPochhammer_eval_neg_one, Nat.factorial_succ]
  push_cast
  field_simp

/-- `Lb (bin k) = (-1)^k/(k+1)`. -/
theorem Lb_bin (k : ℕ) : Lb (bin k) = (-1) ^ k / (k + 1 : ℚ) := by
  have h := Lb_shift (bin (k + 1))
  rw [bin_comp_add_one, Lb_add, bin_derivative_eval_zero] at h
  linarith

/-- A polynomial invariant under `x ↦ x + 1` is constant. -/
lemma eq_C_of_comp_add_one {Q : ℚ[X]} (h : Q.comp (X + 1) = Q) : Q = C (Q.eval 0) := by
  apply poly_eq_of_nat
  intro m
  rw [eval_C]
  induction m with
  | zero => simp
  | succ m ih =>
    have := congrArg (eval (m : ℚ)) h
    rw [eval_comp, eval_add, eval_X, eval_one] at this
    push_cast; rw [this, ih]

/-- **Derivative of the binomial polynomials**. -/
theorem derivative_bin (k : ℕ) :
    (bin k).derivative = ∑ j ∈ Icc 1 k, C (dcoef j) * bin (k - j) := by
  induction k with
  | zero => simp [bin]
  | succ k ih =>
    set D := (bin (k + 1)).derivative - ∑ j ∈ Icc 1 (k + 1), C (dcoef j) * bin (k + 1 - j) with hD
    suffices hD0 : D = 0 by rw [hD] at hD0; exact sub_eq_zero.mp hD0
    have hcomp : D.comp (X + 1) = D := by
      rw [hD, sub_comp, Polynomial.sum_comp]
      have h1 : (bin (k + 1)).derivative.comp (X + 1) = (bin (k + 1)).derivative + (bin k).derivative := by
        have := congrArg derivative (bin_comp_add_one k)
        rw [derivative_comp, derivative_add, derivative_X, derivative_one, add_zero, one_mul,
          derivative_add] at this
        exact this
      rw [h1, ih]
      have h2 : ∀ j ∈ Icc 1 (k + 1), (C (dcoef j) * bin (k + 1 - j)).comp (X + 1) =
          C (dcoef j) * bin (k + 1 - j) + (if j ≤ k then C (dcoef j) * bin (k - j) else 0) := by
        intro j hj
        rw [mul_comp, C_comp]
        rw [Finset.mem_Icc] at hj
        split_ifs with hjk
        · obtain ⟨i, hi⟩ : ∃ i, k + 1 - j = i + 1 := ⟨k - j, by omega⟩
          rw [hi, bin_comp_add_one, show k - j = i by omega]; ring
        · have : k + 1 - j = 0 := by omega
          rw [this, bin_zero, one_comp]; simp
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      have h3 : ∑ j ∈ Icc 1 (k + 1), (if j ≤ k then C (dcoef j) * bin (k - j) else 0) =
          ∑ j ∈ Icc 1 k, C (dcoef j) * bin (k - j) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [h3]; ring
    have h0 : D.eval 0 = 0 := by
      rw [hD, eval_sub, eval_finsetSum, bin_derivative_eval_zero,
        ← Finset.sum_erase_add _ _ (show k + 1 ∈ Icc 1 (k + 1) by simp)]
      rw [Finset.sum_eq_zero]
      · simp [bin_zero, dcoef]
      · intro j hj
        rw [Finset.mem_erase, Finset.mem_Icc] at hj
        rw [eval_mul, bin_eval_zero (by omega), mul_zero]
    rw [eq_C_of_comp_add_one hcomp, h0, C_0]

/-! ### Newton expansion -/

/-- **Newton expansion** of a polynomial in the binomial basis. -/
theorem newton (P : ℚ[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    P = ∑ k ∈ range (d + 1), C ((fwdDiff 1)^[k] P.eval 0) * bin k := by
  apply poly_eq_of_nat
  intro m
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ)) P.eval m 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [h, eval_finsetSum]
  simp only [eval_mul, eval_C, bin_eval_nat]
  have hz : ∀ k, d < k → (fwdDiff 1)^[k] P.eval 0 = 0 := fun k hk => by
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]; rfl
  have hz' : ∀ k, m < k → (m.choose k : ℚ) = 0 := fun k hk => by
    rw [Nat.choose_eq_zero_of_lt hk]; simp
  have e1 : ∑ k ∈ range (m + 1), (m.choose k : ℚ) * (fwdDiff 1)^[k] P.eval 0 =
      ∑ k ∈ range (m + d + 1), (m.choose k : ℚ) * (fwdDiff 1)^[k] P.eval 0 := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hz' k (by omega), zero_mul]
  have e2 : ∑ k ∈ range (d + 1), (fwdDiff 1)^[k] P.eval 0 * (m.choose k : ℚ) =
      ∑ k ∈ range (m + d + 1), (fwdDiff 1)^[k] P.eval 0 * (m.choose k : ℚ) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hz k (by omega), zero_mul]
  rw [e1, e2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
lemma D_monic (K : ℕ) : (D K).Monic := by
  unfold D; exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C _

lemma natDegree_D (K : ℕ) : (D K).natDegree = K := by
  unfold D; rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega
lemma eval_D (m : ℕ) (x : ℚ) : (D m).eval x = ∏ j ∈ Icc 1 m, (x + (j : ℚ) ^ 2) := by
  simp [D, eval_prod]

lemma eval_D_eq_zero {m j : ℕ} (hj : j ∈ Icc 1 m) : (D m).eval (-(j : ℚ) ^ 2) = 0 := by
  rw [eval_D]
  exact Finset.prod_eq_zero hj (by ring)

lemma eval_D_ne_zero {m j : ℕ} (hj : m < j) : (D m).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_D]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : (i : ℚ) < j := by exact_mod_cast (by omega : i < j)
  have h2 : (0 : ℚ) ≤ i := by positivity
  nlinarith

lemma eval_derivative_D {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) = ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  rw [D, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single j]
  · simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_mul, eval_one, mul_one,
      eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro b _ hb
    rw [eval_mul, eval_prod]
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb.symm, hj⟩) (by simp)) _
  · intro h; exact absurd hj h

lemma eval_derivative_D_ne_zero {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_derivative_D hj]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  have : (i : ℚ) ≠ j := by exact_mod_cast hij
  have h0i : (0 : ℚ) ≤ i := by positivity
  have h0j : (0 : ℚ) ≤ j := by positivity
  intro h
  have hfac : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact this (by linarith)
  · have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    linarith

lemma modByMonic_eq_sum_res (K : ℕ) (P : ℚ[X]) :
    P %ₘ D K = ∑ j ∈ Icc 1 K, C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2)) := by
  have hnodes : Set.InjOn (fun j : ℕ => -(j : ℚ) ^ 2) (Icc 1 K : Set ℕ) := by
    intro a _ b _ hab
    have h1 : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := by simpa using hab
    have h2 : a ^ 2 = b ^ 2 := by exact_mod_cast h1
    exact Nat.pow_left_injective two_ne_zero h2
  set s : Finset ℚ := (Icc 1 K).image (fun j : ℕ => -(j : ℚ) ^ 2) with hs
  have hcard : s.card = K := by
    rw [hs, Finset.card_image_of_injOn hnodes]; simp
  -- degree of each summand
  have hterm : ∀ j ∈ Icc 1 K,
      (C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree < K := by
    intro j hj
    have hK : 1 ≤ K := (Finset.mem_Icc.mp hj).2.trans' (Finset.mem_Icc.mp hj).1
    have hprod : (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).natDegree = K - 1 := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
      simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hj, Nat.card_Icc]
      omega
    calc (C (res K P j) * ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree
        ≤ (C (res K P j)).degree + (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).degree :=
          degree_mul_le _ _
      _ ≤ 0 + ((K - 1 : ℕ) : WithBot ℕ) := by
          gcongr
          · exact degree_C_le
          · rw [← hprod]; exact degree_le_natDegree
      _ < K := by
          rw [zero_add]; exact_mod_cast (by omega : K - 1 < K)
  refine eq_of_degree_sub_lt_of_eval_finset_eq s ?_ ?_
  · rw [hcard]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rcases eq_or_ne (P %ₘ D K) 0 with h | h
      · rw [h, degree_zero]; exact WithBot.bot_lt_coe _
      · have := degree_modByMonic_lt P (D_monic K)
        rwa [degree_eq_natDegree (D_monic K).ne_zero, natDegree_D] at this
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr hterm
  · intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨j₀, hj₀, rfl⟩ := hx
    -- LHS: `(P %ₘ D_K)(-j₀²) = P(-j₀²)`
    have hL : (P %ₘ D K).eval (-(j₀ : ℚ) ^ 2) = P.eval (-(j₀ : ℚ) ^ 2) := by
      conv_rhs => rw [← modByMonic_add_div P (D K)]
      rw [eval_add, eval_mul, eval_D_eq_zero hj₀, zero_mul, add_zero]
    rw [hL, eval_finsetSum, Finset.sum_eq_single j₀]
    · rw [eval_mul, eval_C, eval_prod, res, eval_derivative_D hj₀]
      have hne := eval_derivative_D_ne_zero hj₀
      rw [eval_derivative_D hj₀] at hne
      have : ∏ i ∈ (Icc 1 K).erase j₀, eval (-(j₀ : ℚ) ^ 2) (X + C ((i : ℚ) ^ 2)) =
          ∏ i ∈ (Icc 1 K).erase j₀, ((i : ℚ) ^ 2 - (j₀ : ℚ) ^ 2) :=
        Finset.prod_congr rfl fun i _ => by simp; ring
      rw [this, div_mul_cancel₀ _ hne]
    · intro j hj hjne
      rw [eval_mul, eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := j₀) ?_ ?_)
      · exact Finset.mem_erase.mpr ⟨fun h => hjne h.symm, hj₀⟩
      · simp
    · intro h; exact absurd hj₀ h

lemma piPl_monic (Pl : Finset ℤ) : (piPl Pl).Monic :=
  monic_prod_of_monic _ _ fun r _ => monic_X_sub_C _

lemma natDegree_piPl (Pl : Finset ℤ) : (piPl Pl).natDegree = Pl.card := by
  unfold piPl
  rw [natDegree_prod_of_monic _ _ fun r _ => monic_X_sub_C _]
  rw [Finset.sum_congr rfl fun (r : ℤ) _ => natDegree_X_sub_C ((r : ℤ) : ℚ)]
  simp

lemma lagrange_basis_eq (Pl : Finset ℤ) (r : ℤ) :
    Lagrange.basis Pl (fun s : ℤ => (s : ℚ)) r =
      C (∏ s ∈ Pl.erase r, ((r : ℚ) - s))⁻¹ * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]

theorem partial_fractionsP (A : ℚ[X]) (Pl : Finset ℤ) :
    A = polyPart A Pl * piPl Pl +
      ∑ r ∈ Pl, C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
  have hinj : Set.InjOn (fun s : ℤ => (s : ℚ)) Pl := fun a _ b _ h => by
    simpa using h
  have hmod : A %ₘ piPl Pl = ∑ r ∈ Pl, C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
    rw [Lagrange.eq_interpolate_of_eval_eq (f := A %ₘ piPl Pl) (fun r : ℤ => A.eval (r : ℚ)) hinj
      (by
        have := degree_modByMonic_lt A (piPl_monic Pl)
        rwa [degree_eq_natDegree (piPl_monic Pl).ne_zero, natDegree_piPl] at this)
      (fun r hr => by
        have h1 := modByMonic_add_div A (piPl Pl)
        have h2 : (piPl Pl).eval (r : ℚ) = 0 := by
          unfold piPl; rw [eval_prod]
          exact Finset.prod_eq_zero hr (by simp)
        conv_rhs => rw [← h1]
        rw [eval_add, eval_mul, h2, zero_mul, add_zero])]
    simp only [Lagrange.interpolate_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [lagrange_basis_eq, resP, div_eq_mul_inv, C_mul, mul_assoc]
  conv_lhs => rw [← modByMonic_add_div A (piPl Pl)]
  rw [hmod, polyPart, add_comm, mul_comm]

lemma natDegree_polyPart_le (A : ℚ[X]) (Pl : Finset ℤ) :
    (polyPart A Pl).natDegree ≤ A.natDegree - Pl.card := by
  unfold polyPart
  rw [natDegree_divByMonic A (piPl_monic Pl), natDegree_piPl]

lemma tau_add (P Q : ℚ[X]) : tau (P + Q) = tau P + tau Q := by
  unfold tau
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    derivative_add, Lb_add]
  ring

lemma tau_C_mul (c : ℚ) (P : ℚ[X]) : tau (C c * P) = c * tau P := by
  unfold tau
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    derivative_C_mul, Lb_C_mul]
  ring

lemma tau_neg (P : ℚ[X]) : tau (-P) = -tau P := by
  rw [show -P = C (-1) * P by simp, tau_C_mul]; ring

lemma tau_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) : tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tau, Lb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tau_add, ih]

lemma tau_X_pow (n : ℕ) :
    tau (X ^ n) = (n.descFactorial 3 : ℚ) * _root_.bernoulli (n - 3) / 24 := by
  unfold tau
  rw [iterate_derivative_X_pow_eq_smul, Lb_smul, Lb_X_pow]

lemma tau_X_pow_odd (e : ℕ) : tau (C ((-1 : ℚ) ^ e) * X ^ (2 * e + 5)) = μmono e := by
  rw [tau_C_mul, tau_X_pow, μmono]
  rw [show 2 * e + 5 - 3 = 2 * e + 2 by omega,
    show (2 * e + 5).descFactorial 3 = (2 * e + 5) * (2 * e + 4) * (2 * e + 3) by
      simp [Nat.descFactorial]; ring]
  push_cast
  ring

/-- `τ(x⁵ Q(-x²)) = μ(Q)`. -/
lemma tau_pull_poly (Q : ℚ[X]) : tau (X ^ 5 * Q.comp (-X ^ 2)) = μpoly Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, mul_add, tau_add, hP, hQ]
    unfold μpoly
    rw [Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)]
  | monomial e a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp]
    have : X ^ 5 * (C a * (-X ^ 2) ^ e) = C a * (C ((-1 : ℚ) ^ e) * X ^ (2 * e + 5)) := by
      rw [neg_pow, ← pow_mul, map_pow, map_neg, map_one]; ring
    rw [this, tau_C_mul, tau_X_pow_odd]
    unfold μpoly
    rw [C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_index _ _ (by simp)]

lemma tau_cubic (a : ℚ) : tau (-X ^ 3 - C a * X) = -1 / 4 := by
  rw [sub_eq_add_neg, tau_add, tau_neg, tau_neg, tau_C_mul, tau_X_pow,
    show (X : ℚ[X]) = X ^ 1 by ring, tau_X_pow]
  simp [Nat.descFactorial, _root_.bernoulli_zero]
  norm_num

/-! ### The pole set `{±1, …, ±K}` -/

lemma PlK_disjoint (K : ℕ) :
    Disjoint ((Icc 1 K).image (fun j : ℕ => (j : ℤ))) ((Icc 1 K).image (fun j : ℕ => -(j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, hab⟩ := h2
  rw [Finset.mem_Icc] at ha hb
  omega

lemma sum_PlK {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∑ r ∈ PlK K, f r = ∑ j ∈ Icc 1 K, (f j + f (-j)) := by
  rw [PlK, Finset.sum_union (PlK_disjoint K), Finset.sum_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.sum_add_distrib]

lemma prod_PlK {M : Type*} [CommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∏ r ∈ PlK K, f r = ∏ j ∈ Icc 1 K, (f j * f (-j)) := by
  rw [PlK, Finset.prod_union (PlK_disjoint K), Finset.prod_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.prod_image (fun a _ b _ h => by simpa using h), Finset.prod_mul_distrib]

lemma X_add_C_comp_neg_sq (a : ℚ) : (X + C a).comp (-X ^ 2) = -X ^ 2 + C a := by simp

lemma piPl_PlK (K : ℕ) : piPl (PlK K) = C ((-1 : ℚ) ^ K) * (D K).comp (-X ^ 2) := by
  unfold piPl D
  rw [prod_PlK, Polynomial.prod_comp, show C ((-1 : ℚ) ^ K) = ∏ j ∈ Icc 1 K, C (-1 : ℚ) by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, map_pow],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [X_add_C_comp_neg_sq]
  push_cast
  rw [C_neg, C_pow, map_neg, map_one]
  ring

lemma card_PlK (K : ℕ) : (PlK K).card = 2 * K := by
  rw [PlK, Finset.card_union_of_disjoint (PlK_disjoint K),
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp; ring

lemma piPl_eq_Bj {K j : ℕ} (hj : j ∈ Icc 1 K) :
    piPl (PlK K) = (-X ^ 2 + C ((j : ℚ) ^ 2)) * Bj K j := by
  rw [piPl_PlK, Bj, D, ← Finset.mul_prod_erase _ _ hj, mul_comp, X_add_C_comp_neg_sq]; ring

lemma natDegree_Bj_le {K j : ℕ} (hj : j ∈ Icc 1 K) : (Bj K j).natDegree ≤ 2 * (K - 1) := by
  unfold Bj
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  have h1 : (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).natDegree ≤ K - 1 := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun (i : ℕ) _ => (natDegree_X_add_C (((i : ℕ) : ℚ) ^ 2)).le).trans ?_
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hj]; simp
  have h2 : (-X ^ 2 : ℚ[X]).natDegree = 2 := by rw [natDegree_neg, natDegree_X_pow]
  rw [h2]; omega

/-- The polynomial part of the pulled-back function. -/
theorem polyPart_pull (K : ℕ) (P : ℚ[X]) :
    polyPart (pull K P) (PlK K) = X ^ 5 * (P /ₘ D K).comp (-X ^ 2) +
      ∑ j ∈ Icc 1 K, C (res K P j) * (-X ^ 3 - C ((j : ℚ) ^ 2) * X) := by
  unfold polyPart
  refine (div_modByMonic_unique _
    (∑ j ∈ Icc 1 K, C (res K P j) * (C ((j : ℚ) ^ 4) * X * Bj K j)) (piPl_monic _) ⟨?_, ?_⟩).1
  · have hP := modByMonic_add_div P (D K)
    rw [modByMonic_eq_sum_res] at hP
    conv_rhs => rw [pull, ← hP]
    rw [add_comp, mul_comp, Polynomial.sum_comp, piPl_PlK]
    simp only [mul_comp, C_comp, mul_add, Finset.mul_sum]
    have hj : ∀ j ∈ Icc 1 K, C ((-1 : ℚ) ^ K) * X ^ 5 *
        (C (res K P j) * (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))).comp (-X ^ 2)) =
        C (res K P j) * (C ((j : ℚ) ^ 4) * X * Bj K j) +
          C ((-1 : ℚ) ^ K) * (D K).comp (-X ^ 2) *
            (C (res K P j) * (-X ^ 3 - C ((j : ℚ) ^ 2) * X)) := by
      intro j hjK
      have := piPl_eq_Bj hjK
      rw [piPl_PlK] at this
      rw [this, Bj]
      have e : (C ((j : ℚ) ^ 4) : ℚ[X]) = C ((j : ℚ) ^ 2) * C ((j : ℚ) ^ 2) := by
        rw [← C_mul]; ring_nf
      rw [e]; ring
    rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib]
    ring
  · rw [degree_eq_natDegree (piPl_monic _).ne_zero, natDegree_piPl, card_PlK]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · refine (degree_le_natDegree).trans_lt ?_
      have : (∑ j ∈ Icc 1 K, C (res K P j) * (C ((j : ℚ) ^ 4) * X * Bj K j)).natDegree ≤
          2 * K - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun j hjK => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_mul_le).trans ?_
        refine (Nat.add_le_add ((natDegree_C_mul_le _ _).trans natDegree_X_le)
          (natDegree_Bj_le hjK)).trans ?_
        omega
      exact_mod_cast (Nat.lt_of_le_of_lt this (by omega))

lemma prod_erase_eq_derivative (Pl : Finset ℤ) {r : ℤ} (hr : r ∈ Pl) :
    ∏ s ∈ Pl.erase r, ((r : ℚ) - s) = (derivative (piPl Pl)).eval (r : ℚ) := by
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (s := Pl) (v := fun s : ℤ => (s : ℚ)) hr
  rw [show piPl Pl = Lagrange.nodal Pl (fun s : ℤ => (s : ℚ)) from rfl, h, Lagrange.eval_nodal]

lemma resP_pull (K : ℕ) (P : ℚ[X]) {r : ℤ} (hr : r ∈ PlK K) (hr0 : r ≠ 0) :
    resP (pull K P) (PlK K) r =
      -((r : ℚ) ^ 4 / 2) * (P.eval (-(r : ℚ) ^ 2) / (derivative (D K)).eval (-(r : ℚ) ^ 2)) := by
  unfold resP
  rw [prod_erase_eq_derivative _ hr, piPl_PlK, derivative_C_mul, derivative_comp, eval_mul,
    eval_C, eval_mul, eval_comp, pull, eval_mul, eval_mul, eval_C, eval_pow, eval_X, eval_comp]
  simp only [derivative_neg, derivative_X_pow, eval_neg, eval_mul, eval_C, eval_pow, eval_X]
  have hr0' : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
  have hK : ((-1 : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hD : (derivative (D K)).eval (-(r : ℚ) ^ 2) = 0
  · rw [hD]; simp
  · field_simp
    norm_num
    ring

lemma dd_nat (j : ℕ) : dd (j : ℤ) = j := by simp [dd]

lemma dd_neg {j : ℕ} (hj : 1 ≤ j) : dd (-(j : ℤ)) = j - 1 := by
  unfold dd
  rw [if_neg (by omega)]
  omega

lemma H5_succ_eq {j : ℕ} (hj : 1 ≤ j) : H5 j = H5 (j - 1) + 1 / (j : ℚ) ^ 5 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold H5
  rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]

/-- **The pullback identity (3.1)**: `μ_X(P / D_K) = τ_X((-1)^K x⁵ P(-x²) / ∏_{r ∈ PlK} (x - r))`. -/
theorem μX_eq_tauX (K : ℕ) (P : ℚ[X]) : μX K P = tauX (pull K P) (PlK K) := by
  unfold μX tauX
  rw [polyPart_pull, tau_add, tau_pull_poly, tau_sum, sum_PlK]
  simp only [tau_C_mul, tau_cubic]
  rw [map_add, map_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjP : (j : ℤ) ∈ PlK K := by
    rw [PlK, Finset.mem_union]; left; exact Finset.mem_image_of_mem _ hj
  have hjN : -(j : ℤ) ∈ PlK K := by
    rw [PlK, Finset.mem_union]; right; exact Finset.mem_image_of_mem _ hj
  rw [resP_pull K P hjP (by omega), resP_pull K P hjN (by omega), dd_nat, dd_neg hj1]
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  unfold poleValue res
  rw [H5_succ_eq hj1]
  push_cast
  ext n
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X, coeff_neg]
  split_ifs <;> first | omega | (field_simp; ring)
end Apery

end Port0

open Finset Polynomial in
/-- The platform target `Apery.muX_eq_tauX`, restated at top level as `solution`. -/
theorem solution (K : ℕ) (P : ℚ[X]) :
    Apery.μX K P = Apery.tauX (Apery.pull K P) (Apery.PlK K) :=
  Apery.μX_eq_tauX K P
