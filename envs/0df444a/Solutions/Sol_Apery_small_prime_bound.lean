-- Prove2me | solution 1 for Apery.small_prime_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T20:03:37.654993+00:00
-- url     : https://prove2.me/submissions/defb2892-17d0-4b28-9a9e-29ed407135ff

/-
# The small-prime bound (3.12) (source `Apery/Arith/SmallPrimeF.lean`)

For every prime $p$ and $n \\ge 1$, the $p$-adic Gauss valuation of the Apery period $F_n$
is at least $-(6\\,(37n)\\log_p(200n) + 37n\\,v_p(24))$. The file ports the basis
$q_P$, its integrality (`VG_qP_eval`, `VG_D_eval`), the determinant identity
`det_coeffMat_qP`, the squared leading coefficients (`prod_qlead_sq`, `S_eq_qlead`) and the
theorem, importing the already-proved `Apery.crude_tauX` and `Apery.muX_eq_tauX`. Faithful port
of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit
import Theorems.Thm_Apery_crude_tauX
import Theorems.Thm_Apery_muX_eq_tauX

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Polynomial Matrix Finset

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

lemma GV.pow {F : ℚ[X]} {r : ℚ} (h : GV p F r) (n : ℕ) : GV p (F ^ n) (n * r) := by
  induction n with
  | zero => simpa using GV.C (p := p) (VG.one (p := p))
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

lemma GV.comp {F G : ℚ[X]} (hF : GV p F 0) (hG : GV p G 0) : GV p (F.comp G) 0 := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine GV.sum _ fun n _ => ?_
  have := GV.C_mul (hF n) (hG.pow n)
  simpa using this

lemma VG.eval {F : ℚ[X]} {z : ℚ} (hF : GV p F 0) (hz : VG p z 0) : VG p (F.eval z) 0 := by
  rw [eval_eq_sum, Polynomial.sum]
  refine VG.sum _ fun n _ => ?_
  have := (hF n).mul (hz.pow n)
  simpa using this

lemma VG.eval_zero {F : ℚ[X]} {r : ℚ} (hF : GV p F r) : VG p (F.eval 0) r := by
  rw [← coeff_zero_eq_eval_zero]; exact hF 0

lemma GV.divByMonic_X_sub_C {F : ℚ[X]} {a : ℚ} (hF : GV p F 0) (ha : VG p a 0) :
    GV p (F /ₘ (Polynomial.X - Polynomial.C a)) 0 := fun n => by
  rw [coeff_divByMonic_X_sub_C]
  refine VG.sum _ fun i _ => ?_
  have := (ha.pow (i - (n + 1))).mul (hF i)
  simpa using this

/-- An integral polynomial vanishing at `p`-integral distinct points is divisible by
`∏ (X - ρ)` with an integral quotient. -/
theorem factor_roots (ρs : Finset ℚ) (hρ : ∀ ρ ∈ ρs, VG p ρ 0) {F : ℚ[X]} (hF : GV p F 0)
    (hroot : ∀ ρ ∈ ρs, F.eval ρ = 0) :
    ∃ S : ℚ[X], GV p S 0 ∧ F = (∏ ρ ∈ ρs, (X - C ρ)) * S := by
  classical
  induction ρs using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hF, by simp⟩
  | insert a ρs ha ih =>
    have hra : F.IsRoot a := hroot a (Finset.mem_insert_self _ _)
    set F1 := F /ₘ (X - C a) with hF1
    have hFeq : F = (X - C a) * F1 := ((mul_divByMonic_eq_iff_isRoot).mpr hra).symm
    have hF1int : GV p F1 0 := GV.divByMonic_X_sub_C hF (hρ a (Finset.mem_insert_self _ _))
    have hF1root : ∀ ρ ∈ ρs, F1.eval ρ = 0 := by
      intro ρ hρs
      have h1 := hroot ρ (Finset.mem_insert_of_mem hρs)
      rw [hFeq, eval_mul, eval_sub, eval_X, eval_C] at h1
      have hne : ρ - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ hρs)
      exact (mul_eq_zero.mp h1).resolve_left hne
    obtain ⟨S, hS, hSeq⟩ := ih (fun ρ h => hρ ρ (Finset.mem_insert_of_mem h)) hF1int hF1root
    exact ⟨S, hS, by rw [hFeq, hSeq, Finset.prod_insert ha, mul_assoc]⟩

/-- Multiset products. -/
lemma GV.multiset_prod (s : Multiset ℚ[X]) (b : ℚ[X] → ℚ) (h : ∀ f ∈ s, GV p f (b f)) :
    GV p s.prod (s.map b).sum := by
  induction s using Multiset.induction_on with
  | empty => simpa using GV.C (p := p) (VG.one (p := p))
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul (ih fun f hf => h f (Multiset.mem_cons_of_mem hf))

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
lemma bin_eval_int (k : ℕ) (z : ℤ) : ∃ w : ℤ, (bin k).eval (z : ℚ) = w := by
  induction k generalizing z with
  | zero => exact ⟨1, by simp [bin_zero]⟩
  | succ k ih =>
    have hstep : ∀ y : ℚ, (bin (k + 1)).eval (y + 1) = (bin (k + 1)).eval y + (bin k).eval y := by
      intro y
      have := congrArg (eval y) (bin_comp_add_one k)
      rw [eval_comp, eval_add, eval_X, eval_one, eval_add] at this
      exact this
    induction z using Int.induction_on with
    | zero => exact ⟨0, by rw [Int.cast_zero, bin_eval_zero (by omega)]⟩
    | succ i hi =>
      obtain ⟨w, hw⟩ := hi
      obtain ⟨w', hw'⟩ := ih (i : ℤ)
      refine ⟨w + w', ?_⟩
      push_cast at hw hw' ⊢
      rw [hstep, hw, hw']
    | pred i hi =>
      obtain ⟨w, hw⟩ := hi
      obtain ⟨w', hw'⟩ := ih (-(i : ℤ) - 1)
      refine ⟨w - w', ?_⟩
      have := hstep ((-(i : ℤ) - 1 : ℤ) : ℚ)
      push_cast at this hw hw' ⊢
      rw [show (-(i : ℚ) - 1 + 1) = -(i : ℚ) by ring, hw] at this
      linarith

lemma VG_bin_eval_int (k : ℕ) (z : ℤ) : VG p ((bin k).eval (z : ℚ)) 0 := by
  obtain ⟨w, hw⟩ := bin_eval_int k z
  rw [hw]; exact VG.intCast w

lemma log_mono {a b : ℕ} (h : a ≤ b) : (Nat.log p a : ℚ) ≤ Nat.log p b := by
  exact_mod_cast Nat.log_mono_right h

lemma coeff_det_of_natDegree_le_one {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    (M.det).coeff n = (Matrix.of fun i j => (M i j).coeff 1).det ∧ M.det.natDegree ≤ n := by
  constructor
  · rw [det_apply', det_apply', finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hc := coeff_prod_of_natDegree_le (s := Finset.univ) (f := fun i => M (σ i) i) (n := 1)
      (fun i _ => hM _ _)
    simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hc
    rw [← C_eq_intCast, coeff_C_mul, hc]
    simp
  · rw [det_apply']
    refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_intCast, zero_add]
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i : Fin n, (M (σ i) i).natDegree ≤ ∑ i : Fin n, 1 := Finset.sum_le_sum fun i _ => hM _ _
      _ = n := by simp
lemma poleValue_eq (j : ℕ) : poleValue j =
    C ((j : ℚ) ^ 4) * X + C (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * (j : ℚ))) := by
  simp only [poleValue, C_add, C_sub, C_mul, C_neg, C_pow]
  ring

lemma μX_eq (K : ℕ) (P : ℚ[X]) : μX K P =
    C (∑ j ∈ Icc 1 K, res K P j * (j : ℚ) ^ 4) * X +
    C (μpoly (P /ₘ D K) +
      ∑ j ∈ Icc 1 K, res K P j * (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * (j : ℚ)))) := by
  simp only [μX, res, poleValue_eq, mul_add, ← mul_assoc, ← C_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← map_sum, C_add]
  ring

lemma natDegree_μX_le (K : ℕ) (P : ℚ[X]) : (μX K P).natDegree ≤ 1 := by
  rw [μX_eq]
  compute_degree!

lemma coeff_μX_one (K : ℕ) (P : ℚ[X]) :
    (μX K P).coeff 1 = ∑ j ∈ Icc 1 K, res K P j * (j : ℚ) ^ 4 := by
  rw [μX_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, mul_one, one_ne_zero, ite_false, add_zero]

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

/-- Reindexing: a sum over `Icc 1 K` whose terms vanish on `Icc 1 N` is a sum over
`k : Fin (K - N)` of the terms at `N + 1 + k`. -/
lemma sum_Icc_eq_sum_fin (N K : ℕ) (hNK : N ≤ K) (f : ℕ → ℚ) (hf : ∀ j ∈ Icc 1 N, f j = 0) :
    ∑ j ∈ Icc 1 K, f j = ∑ k : Fin (K - N), f (N + 1 + k) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (N + 1 + k)) (K - N)]
  have h1 := Finset.sum_Ico_eq_sum_range f (N + 1) (K + 1)
  rw [show K + 1 - (N + 1) = K - N by omega] at h1
  rw [← h1]
  have h2 : Icc 1 K = Ico 1 (K + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h2, ← Finset.sum_Ico_consecutive f (show 1 ≤ N + 1 by omega) (show N + 1 ≤ K + 1 by omega)]
  rw [Finset.sum_eq_zero (fun j hj => hf j ?_), zero_add]
  rw [Finset.mem_Ico] at hj
  rw [Finset.mem_Icc]; omega

lemma natDegree_G_le (n : ℕ) (i j : Fin (37 * n)) : (G n i j).natDegree ≤ 1 :=
  natDegree_μX_le _ _

/-- The matrix of `X`-coefficients of `G_K(X)` is `Vᵀ diag(w) V` with `V` the Vandermonde
matrix of the nodes. -/
lemma coeff_G_one (n : ℕ) : (Matrix.of fun i j : Fin (37 * n) => (G n i j).coeff 1) =
    (vandermonde (node n))ᵀ * diagonal (weight n) * vandermonde (node n) := by
  ext i j
  simp only [Matrix.of_apply, G, coeff_μX_one, res]
  rw [sum_Icc_eq_sum_fin (3 * n) (40 * n) (by omega)
    (fun j' => eval (-(j' : ℚ) ^ 2) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) /
      eval (-(j' : ℚ) ^ 2) (derivative (D (40 * n))) * (j' : ℚ) ^ 4)
    (fun j' hj' => by rw [eval_mul, eval_pow, eval_D_eq_zero hj']; simp)]
  rw [show 40 * n - 3 * n = 37 * n by omega]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, vandermonde_apply, weight, node,
    eval_mul, eval_pow, eval_X]
  rw [pow_add]
  ring

lemma node_injective (n : ℕ) : Function.Injective (node n) := by
  intro k₁ k₂ h
  simp only [node, neg_inj] at h
  have h' : (3 * n + 1 + (k₁ : ℕ)) ^ 2 = (3 * n + 1 + (k₂ : ℕ)) ^ 2 := by exact_mod_cast h
  have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h'
  exact Fin.ext (by omega)

lemma weight_ne_zero (n : ℕ) (k : Fin (37 * n)) : weight n k ≠ 0 := by
  have hk := k.isLt
  have h1 : (D (3 * n)).eval (node n k) ≠ 0 := eval_D_ne_zero (by omega)
  have h2 : (derivative (D (40 * n))).eval (node n k) ≠ 0 :=
    eval_derivative_D_ne_zero (by rw [Finset.mem_Icc]; omega)
  have h3 : ((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ≠ 0 := by positivity
  unfold weight
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h3)) h2

lemma det_coeff_G_one_ne_zero (n : ℕ) :
    (Matrix.of fun i j : Fin (37 * n) => (G n i j).coeff 1).det ≠ 0 := by
  rw [coeff_G_one, det_mul, det_mul, det_transpose, det_diagonal]
  have hV : (vandermonde (node n)).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr (node_injective n)
  exact mul_ne_zero (mul_ne_zero hV (Finset.prod_ne_zero_iff.mpr fun k _ => weight_ne_zero n k)) hV

/-- **(2.9)**: `Δ_K` has degree exactly `h = 37 n`. -/
theorem natDegree_Δ (n : ℕ) : (Δ n).natDegree = 37 * n := by
  obtain ⟨hc, hd⟩ := coeff_det_of_natDegree_le_one (G n) (natDegree_G_le n)
  exact natDegree_eq_of_le_of_coeff_ne_zero hd (hc ▸ det_coeff_G_one_ne_zero n)

lemma S_pos (n : ℕ) : 0 < S n := by
  unfold S
  positivity

/-- **(2.9)**: `F_K` has degree exactly `h = 37 n`. -/
theorem natDegree_F (n : ℕ) : (F n).natDegree = 37 * n := by
  rw [F, natDegree_C_mul (S_pos n).ne', natDegree_Δ]

lemma D_monic (K : ℕ) : (D K).Monic := by
  unfold D; exact monic_prod_of_monic _ _ fun j _ => monic_X_add_C _

lemma natDegree_D (K : ℕ) : (D K).natDegree = K := by
  unfold D; rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega

/-- The polynomial identity behind the partial fractions: the remainder `P %ₘ D_K` equals
`∑_j res_j ∏_{i ≠ j} (X + i²)`. -/
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

lemma aeval_D_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < aeval t (D m) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  refine Finset.prod_pos fun j hj => ?_
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  positivity

/-- **Partial fractions** as real functions, for `t ≥ 0`. -/
theorem partial_fractions (K : ℕ) (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t) :
    aeval t P / aeval t (D K) =
      aeval t (P /ₘ D K) + ∑ j ∈ Icc 1 K, (res K P j : ℝ) / (t + (j : ℝ) ^ 2) := by
  have hD : 0 < aeval t (D K) := aeval_D_pos K ht
  have hsplit : aeval t P = aeval t (P %ₘ D K) + aeval t (D K) * aeval t (P /ₘ D K) := by
    conv_lhs => rw [← modByMonic_add_div P (D K)]
    rw [map_add, map_mul]
  rw [hsplit, add_div, mul_div_cancel_left₀ _ hD.ne', add_comm]
  congr 1
  rw [modByMonic_eq_sum_res, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_mul, aeval_C, map_prod]
  simp only [map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  have hj2 : 0 < t + (j : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    positivity
  have hDt : aeval t (D K) = (t + (j : ℝ) ^ 2) * ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) := by
    simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
    rw [← Finset.mul_prod_erase _ _ hj]
  rw [hDt]
  have hprod : 0 < ∏ i ∈ (Icc 1 K).erase j, (t + (i : ℝ) ^ 2) :=
    Finset.prod_pos fun i hi => by
      have : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
      positivity
  field_simp

lemma divByMonic_add' {q : ℚ[X]} (hq : q.Monic) (P Q : ℚ[X]) :
    (P + Q) /ₘ q = P /ₘ q + Q /ₘ q := by
  refine ((div_modByMonic_unique (P /ₘ q + Q /ₘ q) (P %ₘ q + Q %ₘ q) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    have h2 := modByMonic_add_div Q q
    rw [mul_add]; linear_combination h1 + h2
  · exact (degree_add_le _ _).trans_lt (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))

lemma divByMonic_C_mul' {q : ℚ[X]} (hq : q.Monic) (c : ℚ) (P : ℚ[X]) :
    (C c * P) /ₘ q = C c * (P /ₘ q) := by
  refine ((div_modByMonic_unique (C c * (P /ₘ q)) (C c * (P %ₘ q)) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    linear_combination C c * h1
  · rw [← smul_eq_C_mul]; exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)

lemma μpoly_add (P Q : ℚ[X]) : μpoly (P + Q) = μpoly P + μpoly Q := by
  unfold μpoly
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma μpoly_C_mul (c : ℚ) (P : ℚ[X]) : μpoly (C c * P) = c * μpoly P := by
  unfold μpoly
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum,
    Polynomial.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma μX_add (K : ℕ) (P Q : ℚ[X]) : μX K (P + Q) = μX K P + μX K Q := by
  unfold μX
  rw [divByMonic_add' (D_monic K), μpoly_add, map_add]
  simp only [eval_add, add_div, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma μX_C_mul (K : ℕ) (c : ℚ) (P : ℚ[X]) : μX K (C c * P) = C c * μX K P := by
  unfold μX
  rw [divByMonic_C_mul' (D_monic K), μpoly_C_mul, map_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_div_assoc, map_mul]; ring

lemma μX_sum {ι : Type*} (K : ℕ) (s : Finset ι) (f : ι → ℚ[X]) :
    μX K (∑ i ∈ s, f i) = ∑ i ∈ s, μX K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := μX_C_mul K 0 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, μX_add, ih]

/-- The coefficient matrix of a family of polynomials. -/
noncomputable def coeffMat {h : ℕ} (E : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun a k => (E a).coeff k

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X]) (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X ^ (k : ℕ) := by
  conv_lhs => rw [as_sum_range' (E a) h (hE a)]
  rw [Finset.sum_range (fun k => monomial k ((E a).coeff k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeffMat, Matrix.of_apply, C_mul_X_pow_eq_monomial]

/-- **Change of basis**. -/
theorem det_basis_change (n : ℕ) (E : Fin (37 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
      C ((coeffMat E).det ^ 2) * Δ n := by
  set Cm := (coeffMat E).map (C : ℚ →+* ℚ[X]) with hCm
  have hM : (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) =
      Cm * G n * Cm.transpose := by
    refine Matrix.ext fun a b => ?_
    have hexp : D (3 * n) ^ 6 * E a * E b = ∑ k : Fin (37 * n), ∑ l : Fin (37 * n),
        C (coeffMat E a k * coeffMat E b l) * (D (3 * n) ^ 6 * X ^ ((k : ℕ) + (l : ℕ))) := by
      rw [sum_coeffMat E hE a, sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [Matrix.of_apply, hexp, μX_sum]
    simp only [μX_sum, μX_C_mul, Matrix.mul_apply, Matrix.transpose_apply, hCm, Matrix.map_apply, G,
      Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCm, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, Δ, map_pow]; ring
noncomputable def qP (a : ℕ) : ℚ[X] :=
  if a = 0 then 1 else C ((-1 : ℚ) ^ a * 2 / ((2 * a).factorial : ℚ)) * (X * D (a - 1))

/-- Its leading coefficient. -/
noncomputable def qlead (a : ℕ) : ℚ := if a = 0 then 1 else (-1 : ℚ) ^ a * 2 / ((2 * a).factorial : ℚ)

lemma qlead_ne_zero (a : ℕ) : qlead a ≠ 0 := by
  unfold qlead; split_ifs
  · norm_num
  · have : ((2 * a).factorial : ℚ) ≠ 0 := by positivity
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)) this

lemma qP_eq (a : ℕ) : qP a = C (qlead a) * (if a = 0 then 1 else X * D (a - 1)) := by
  unfold qP qlead; split_ifs <;> simp

lemma monic_qbase (a : ℕ) : (if a = 0 then (1 : ℚ[X]) else X * D (a - 1)).Monic := by
  split_ifs
  · exact monic_one
  · exact monic_X.mul (D_monic _)

lemma natDegree_qbase (a : ℕ) : (if a = 0 then (1 : ℚ[X]) else X * D (a - 1)).natDegree = a := by
  split_ifs with h
  · simp [h]
  · rw [natDegree_mul X_ne_zero (D_monic _).ne_zero, natDegree_X, natDegree_D]; omega

lemma natDegree_qP (a : ℕ) : (qP a).natDegree = a := by
  rw [qP_eq, natDegree_C_mul (qlead_ne_zero a), natDegree_qbase]

lemma coeff_qP_self (a : ℕ) : (qP a).coeff a = qlead a := by
  rw [qP_eq, coeff_C_mul]
  have := (monic_qbase a).coeff_natDegree
  rw [natDegree_qbase] at this
  rw [this, mul_one]

/-! ### Integer values -/

lemma prod_Icc_eq_prod_range (N : ℕ) (g : ℕ → ℚ) :
    ∏ j ∈ Icc 1 N, g j = ∏ i ∈ range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

lemma bin_eval_eq (k : ℕ) (y : ℚ) :
    (bin k).eval y = (∏ i ∈ range k, (y - i)) / (k.factorial : ℚ) := by
  unfold bin
  rw [eval_mul, eval_C, descPochhammer_eval_eq_prod_range]
  ring

/-- `∏_{i < 2c+1} (z + c - i) = z ∏_{j ≤ c} (z² - j²)`. -/
lemma prod_window (z : ℚ) (c : ℕ) :
    ∏ i ∈ range (2 * c + 1), (z + c - i) = z * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * (c + 1) + 1 = (2 * c + 1) + 1 + 1 by ring, Finset.prod_range_succ',
      Finset.prod_range_succ]
    have e : ∏ i ∈ range (2 * c + 1), (z + ((c + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) =
        ∏ i ∈ range (2 * c + 1), (z + c - i) := by
      refine Finset.prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e, ih, Finset.prod_Icc_succ_top (by omega)]
    push_cast; ring

/-- `q_a(-z²) = C(z+a, 2a) + C(z+a-1, 2a)` for `a ≥ 1`. -/
lemma qP_eval_neg_sq {a : ℕ} (ha : 1 ≤ a) (z : ℚ) :
    (qP a).eval (-z ^ 2) = (bin (2 * a)).eval (z + a) + (bin (2 * a)).eval (z + a - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [qP, if_neg (by omega), bin_eval_eq, bin_eval_eq, show c + 1 - 1 = c by omega]
  rw [eval_mul, eval_C, eval_mul, eval_X]
  unfold D
  rw [eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have h1 : ∏ i ∈ range (2 * (c + 1)), (z + ((c + 1 : ℕ) : ℚ) - i) =
      (z + ((c + 1 : ℕ) : ℚ)) * (z * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2)) := by
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by ring, Finset.prod_range_succ']
    have e : ∏ i ∈ range (2 * c + 1), (z + ((c + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) =
        ∏ i ∈ range (2 * c + 1), (z + c - i) := by
      refine Finset.prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e, prod_window]; push_cast; ring
  have h2 : ∏ i ∈ range (2 * (c + 1)), (z + ((c + 1 : ℕ) : ℚ) - 1 - i) =
      (z * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2)) * (z - ((c + 1 : ℕ) : ℚ)) := by
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by ring, Finset.prod_range_succ]
    have e : ∏ i ∈ range (2 * c + 1), (z + ((c + 1 : ℕ) : ℚ) - 1 - (i : ℚ)) =
        ∏ i ∈ range (2 * c + 1), (z + c - i) := by
      refine Finset.prod_congr rfl fun i _ => ?_; push_cast; ring
    rw [e, prod_window]; push_cast; ring
  rw [h1, h2]
  have h3 : ∏ j ∈ Icc 1 c, (-z ^ 2 + (j : ℚ) ^ 2) = (-1) ^ c * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2) := by
    rw [show ((-1 : ℚ) ^ c) = ∏ _j ∈ Icc 1 c, (-1 : ℚ) by
      rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel], ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_; ring
  rw [h3]
  have hf : ((2 * (c + 1)).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  have hc : (-1 : ℚ) ^ (c * 2) = 1 := Even.neg_one_pow ⟨c, by ring⟩
  linear_combination (2 * z ^ 2 * ∏ j ∈ Icc 1 c, (z ^ 2 - (j : ℚ) ^ 2)) * hc

lemma VG_qP_eval (a : ℕ) (z : ℤ) : VG p ((qP a).eval (-(z : ℚ) ^ 2)) 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [qP]; exact VG.one
  · rw [qP_eval_neg_sq ha]
    refine VG.add ?_ ?_
    · have := VG_bin_eval_int (p := p) (2 * a) (z + a); push_cast at this; exact this
    · have := VG_bin_eval_int (p := p) (2 * a) (z + a - 1); push_cast at this; exact this

/-- `D_N(-z²) = (N!)² C(N+z, N) C(N-z, N)`. -/
lemma D_eval_neg_sq (N : ℕ) (z : ℚ) :
    (D N).eval (-z ^ 2) = (N.factorial : ℚ) ^ 2 * ((bin N).eval (N + z) * (bin N).eval (N - z)) := by
  rw [bin_eval_eq, bin_eval_eq]
  unfold D
  rw [eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have hf : (N.factorial : ℚ) ≠ 0 := by positivity
  have r1 : ∏ i ∈ range N, ((N : ℚ) + z - i) = ∏ i ∈ range N, (z + ((i + 1 : ℕ) : ℚ)) := by
    rw [← Finset.prod_range_reflect (fun i => z + ((i + 1 : ℕ) : ℚ)) N]
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    push_cast [show i ≤ N - 1 by omega, show 1 ≤ N by omega]; ring
  have r2 : ∏ i ∈ range N, ((N : ℚ) - z - i) = ∏ i ∈ range N, (((i + 1 : ℕ) : ℚ) - z) := by
    rw [← Finset.prod_range_reflect (fun i => ((i + 1 : ℕ) : ℚ) - z) N]
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    push_cast [show i ≤ N - 1 by omega, show 1 ≤ N by omega]; ring
  rw [r1, r2, prod_Icc_eq_prod_range N (fun j => -z ^ 2 + (j : ℚ) ^ 2)]
  field_simp
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

lemma VG_D_eval (N : ℕ) (z : ℤ) :
    VG p ((D N).eval (-(z : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2) 0 := by
  have hf : (N.factorial : ℚ) ≠ 0 := by positivity
  rw [D_eval_neg_sq, mul_div_cancel_left₀ _ (pow_ne_zero _ hf)]
  have h1 := VG_bin_eval_int (p := p) N (N + z)
  have h2 := VG_bin_eval_int (p := p) N (N - z)
  push_cast at h1 h2
  simpa using h1.mul h2

/-! ### Assembly -/

lemma det_coeffMat_qP (h : ℕ) :
    (coeffMat (fun a : Fin h => qP a)).det = ∏ a : Fin h, qlead a := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_congr rfl fun a _ => ?_
    simp only [coeffMat, Matrix.of_apply]
    exact coeff_qP_self a
  · intro i j hij
    simp only [coeffMat, Matrix.of_apply]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_qP]
    exact hij

lemma qlead_sq {a : ℕ} (ha : 1 ≤ a) : qlead a ^ 2 = 4 / (((2 * a).factorial : ℚ) ^ 2) := by
  unfold qlead
  rw [if_neg (by omega), div_pow, mul_pow, ← pow_mul, show a * 2 = 2 * a by ring, pow_mul]
  norm_num

lemma prod_qlead_sq (h : ℕ) (hh : 1 ≤ h) :
    (∏ a : Fin h, qlead a) ^ 2 =
      4 ^ (h - 1) / ∏ i ∈ Icc 1 (h - 1), (((2 * i).factorial : ℚ) ^ 2) := by
  rw [← Finset.prod_pow, Fin.prod_univ_eq_prod_range (fun a => qlead a ^ 2) h]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  rw [Finset.prod_range_succ', show qlead 0 = 1 by simp [qlead], one_pow, mul_one,
    ← prod_Icc_eq_prod_range h' (fun a => qlead a ^ 2), Nat.add_sub_cancel]
  rw [Finset.prod_congr rfl (fun i hi => qlead_sq (Finset.mem_Icc.mp hi).1), Finset.prod_div_distrib,
    Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]

/-- `S_K = ((K!)²/(N!)¹²)^h det(C)²`. -/
lemma S_eq_qlead (n : ℕ) (hn : 1 ≤ n) :
    S n = (((40 * n).factorial : ℚ) ^ 2 / ((3 * n).factorial : ℚ) ^ 12) ^ (37 * n) *
      (∏ a : Fin (37 * n), qlead a) ^ 2 := by
  rw [prod_qlead_sq _ (by omega)]
  unfold S
  have h1 : ((3 * n).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ∏ i ∈ Icc 1 (37 * n - 1), (((2 * i).factorial : ℚ) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [div_pow, ← pow_mul, ← pow_mul, show 12 * (37 * n) = 12 * (37 * n) by rfl]
  field_simp

/-- **The bound (3.12)** at every prime. -/
theorem small_prime_bound {n : ℕ} (hn : 1 ≤ n) :
    GV p (F n) (-(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℚ) + (37 * n : ℕ) * padicValNat p 24)) := by
  set h := 37 * n with hh
  set K := 40 * n with hK
  set N := 3 * n with hN
  set E : Fin h → ℚ[X] := fun a => qP a with hE
  have hEdeg : ∀ a, (E a).natDegree < h := fun a => by rw [hE]; simp only; rw [natDegree_qP]; exact a.isLt
  have hbc := det_basis_change n E hEdeg
  set c : ℚ := (K.factorial : ℚ) ^ 2 / (N.factorial : ℚ) ^ 12 with hc
  set M := Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b) with hM
  have hF : F n = ((C c) • M).det := by
    rw [Matrix.det_smul, hbc, Fintype.card_fin, F, S_eq_qlead n hn, det_coeffMat_qP]
    simp only [map_mul, map_pow]
    ring
  rw [hF]
  set d := 5 + 12 * N + 4 * (h - 1) with hd
  set Λ : ℚ := (Nat.log p (200 * n) : ℚ) with hΛ
  have hd1 : d + 1 ≤ 200 * n := by omega
  have hdK : 2 * K ≤ d := by omega
  have hentry : ∀ a b : Fin h, GV p (((C c) • M) a b)
      ((-3 * Λ - padicValNat p 24 / 2) + (-3 * Λ - padicValNat p 24 / 2)) := by
    intro a b
    rw [Matrix.smul_apply, hM, Matrix.of_apply, smul_eq_mul, ← μX_C_mul, muX_eq_tauX]
    set Q := D (3 * n) ^ 6 * E a * E b with hQ
    set A : ℚ[X] := C ((-1 : ℚ) ^ K / (N.factorial : ℚ) ^ 12) * X ^ 5 * Q.comp (-X ^ 2) with hA
    have hpull : pull (40 * n) (C c * Q) = C ((K.factorial : ℚ) ^ 2) * A := by
      have e1 : C c = C ((K.factorial : ℚ) ^ 2) * C (1 / (N.factorial : ℚ) ^ 12) := by
        rw [← C_mul]; congr 1; rw [hc]; ring
      have e2 : C ((-1 : ℚ) ^ K / (N.factorial : ℚ) ^ 12) =
          C ((-1 : ℚ) ^ (40 * n)) * C (1 / (N.factorial : ℚ) ^ 12) := by
        rw [← C_mul]; congr 1; rw [hK]; ring
      rw [pull, hA, mul_comp, C_comp, e1, e2]; ring
    rw [hpull]
    have hQdeg : Q.natDegree ≤ 6 * N + 2 * (h - 1) := by
      rw [hQ]
      refine (natDegree_mul_le).trans ?_
      have h1 : (D (3 * n) ^ 6 * E a).natDegree ≤ 6 * N + a := by
        refine (natDegree_mul_le).trans ?_
        rw [natDegree_pow, natDegree_D, hE]; simp only; rw [natDegree_qP]
      have h2 : (E b).natDegree ≤ b := by rw [hE]; simp only; rw [natDegree_qP]
      have := a.isLt; have := b.isLt
      omega
    have hAdeg : A.natDegree ≤ d := by
      rw [hA]
      refine (natDegree_mul_le).trans ?_
      have h1 : (C ((-1 : ℚ) ^ K / (N.factorial : ℚ) ^ 12) * X ^ 5 : ℚ[X]).natDegree ≤ 5 :=
        (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow])
      have h2 : (Q.comp (-X ^ 2 : ℚ[X])).natDegree ≤ 2 * (6 * N + 2 * (h - 1)) := by
        rw [natDegree_comp]
        have : (-X ^ 2 : ℚ[X]).natDegree = 2 := by rw [natDegree_neg, natDegree_X_pow]
        rw [this]; linarith
      omega
    have hAint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0 := by
      intro z
      have e : A.eval (z : ℚ) = (-1 : ℚ) ^ K * (z : ℚ) ^ 5 *
          ((D N).eval (-(z : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2) ^ 6 *
          (qP a).eval (-(z : ℚ) ^ 2) * (qP b).eval (-(z : ℚ) ^ 2) := by
        rw [hA, hQ, hE]
        simp only [eval_mul, eval_C, eval_pow, eval_X, eval_comp, eval_neg]
        have : (N.factorial : ℚ) ≠ 0 := by positivity
        field_simp
        rw [hN]; ring
      rw [e]
      have hs : VG p ((-1 : ℚ) ^ K) 0 := by
        rcases neg_one_pow_eq_or ℚ K with h | h <;> rw [h]
        · exact VG.one
        · exact VG.one.neg
      have hz : VG p ((z : ℚ) ^ 5) 0 := by simpa using (VG.intCast (p := p) z).pow 5
      have := (((hs.mul hz).mul ((VG_D_eval (p := p) N z).pow 6)).mul
        (VG_qP_eval (p := p) a z)).mul (VG_qP_eval (p := p) b z)
      simpa using this
    have hb := crude_tauX (p := p) (K := K) (d := d) (by omega) hdK A hAdeg hAint
    refine hb.mono ?_
    have : (Nat.log p (d + 1) : ℚ) ≤ Λ := log_mono hd1
    linarith
  have hdet := det_GV _ (fun _ => -3 * Λ - padicValNat p 24 / 2)
    (fun _ => -3 * Λ - padicValNat p 24 / 2) hentry
  refine hdet.mono ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linarith

end Apery

end Port0

open Polynomial Matrix Finset in
/-- The platform target `Apery.small_prime_bound`, restated at top level as `solution`. -/
theorem solution {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) :
    Apery.GV p (Apery.F n)
      (-(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℚ) + (37 * n : ℕ) * padicValNat p 24)) :=
  Apery.small_prime_bound hn
