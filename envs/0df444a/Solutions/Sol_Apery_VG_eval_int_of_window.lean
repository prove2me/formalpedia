-- Prove2me | solution 1 for Apery.VG_eval_int_of_window
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:57:42.495212+00:00
-- url     : https://prove2.me/submissions/27264770-d348-4a66-9ae6-d00a84bee5cb

/-
# The integer-window valuation lemma `VG_eval_int_of_window` and its toolkit
(`Apery/Arith/SmallPrime.lean` with `BinomialBasis`, `TauBound`, `IntPoly`, `Val`)

If a polynomial $P$ of degree $\le d$ has $p$-adically bounded values at the $d+1$
consecutive integers $s, s+1, \dots, s+d$, then it is bounded at every integer. The file
ports the binomial-basis machinery (`bin`, `Lb`, `dcoef`, `newton`), the Bernoullli/derivative
functional `tau` bound, and the `VG`/`GV` toolkit; part of the small-prime bound used in
`Apery.integral_mN`.

Faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceValToolkit
import Definitions.Def_Zeta5_SourceConstruction

set_option autoImplicit false

section Port0

set_option autoImplicit false

open Finset Polynomial

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

/-- `Lb Q = ∑_n Q_n B_n`. -/
noncomputable def Lb (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * _root_.bernoulli n

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

/-- `bin k = x(x-1)⋯(x-k+1)/k!`. -/
noncomputable def bin (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

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

/-- The coefficients of the derivative in the binomial basis. -/
noncomputable def dcoef (j : ℕ) : ℚ := (-1) ^ (j - 1) / (j : ℚ)

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

noncomputable def tau (P : ℚ[X]) : ℚ := Lb (derivative^[3] P) / 24

/-- `Q` is a combination of `bin 0, …, bin k` with coefficients of valuation `≥ r`. -/
def BinRep (p : ℕ) (k : ℕ) (r : ℚ) (Q : ℚ[X]) : Prop :=
  ∃ e : ℕ → ℚ, Q = ∑ m ∈ range (k + 1), C (e m) * bin m ∧ ∀ m ≤ k, VG p (e m) r

lemma derivative_bin' {k m : ℕ} (hm : m ≤ k) :
    (bin m).derivative = ∑ n ∈ range (k + 1), C (if n < m then dcoef (m - n) else 0) * bin n := by
  rw [derivative_bin]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not (range (k + 1)) (fun n => n < m)]
  rw [Finset.sum_eq_zero (s := (range (k + 1)).filter fun n => ¬ n < m)
    (fun n hn => by rw [Finset.mem_filter] at hn; rw [if_neg hn.2, C_0, zero_mul]), add_zero]
  apply Finset.sum_nbij' (fun n => m - n) (fun j => m - j)
  · intro n hn; simp only [Finset.mem_filter, Finset.mem_range, Finset.coe_filter,
      Set.mem_ofPred_eq] at hn ⊢; simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hj ⊢
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro n hn; simp only [Finset.mem_filter, Finset.mem_range, Finset.coe_filter,
      Set.mem_ofPred_eq] at hn; omega
  · intro j hj; simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hj; omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.coe_filter, Set.mem_ofPred_eq] at hn
    rw [if_pos hn.2, show m - (m - n) = n by omega]

lemma VG_dcoef {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : VG p (dcoef j) (-(Nat.log p k : ℚ)) := by
  unfold dcoef
  rw [div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ (j - 1)) 0 := by
    rcases neg_one_pow_eq_or ℚ (j - 1) with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  simpa using h1.mul (VG.inv_nat hj hjk)

/-- Differentiation loses at most `⌊log_p k⌋` in the binomial basis. -/
theorem BinRep.derivative {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) :
    BinRep p k (r - Nat.log p k) Q.derivative := by
  obtain ⟨e, rfl, he⟩ := h
  refine ⟨fun n => ∑ m ∈ range (k + 1), e m * (if n < m then dcoef (m - n) else 0), ?_, ?_⟩
  · rw [Polynomial.derivative_sum]
    simp_rw [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [Finset.sum_congr rfl fun m hm => by
      rw [derivative_bin' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [C_mul]; ring
  · intro n _
    apply VG.sum
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    split_ifs with hnm
    · have := (he m hmk).mul (VG_dcoef (p := p) (j := m - n) (k := k) (by omega) (by omega))
      simpa [sub_eq_add_neg] using this
    · rw [mul_zero]; exact VG.zero _

/-- The Bernoulli functional loses at most `⌊log_p (k+1)⌋`. -/
theorem BinRep.Lb {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) :
    VG p (Lb Q) (r - Nat.log p (k + 1)) := by
  obtain ⟨e, rfl, he⟩ := h
  rw [Lb_sum]
  apply VG.sum
  intro m hm
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [Lb_C_mul, Lb_bin, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ m) 0 := by
    rcases neg_one_pow_eq_or ℚ m with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have h2 : VG p (((m : ℚ) + 1)⁻¹) (-(Nat.log p (k + 1) : ℚ)) := by
    have := VG.inv_nat (p := p) (j := m + 1) (n := k + 1) (by omega) (by omega)
    simpa using this
  have := (he m hmk).mul (h1.mul h2)
  simpa [sub_eq_add_neg] using this

lemma BinRep.mono {k : ℕ} {r s : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) (hs : s ≤ r) : BinRep p k s Q := by
  obtain ⟨e, he, hv⟩ := h
  exact ⟨e, he, fun m hm => (hv m hm).mono hs⟩

/-- Values at `0, …, d` give a binomial representation. -/
theorem binRep_of_values {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) : BinRep p d β P := by
  refine ⟨fun k => (fwdDiff 1)^[k] P.eval 0, newton P hd, fun k hk => ?_⟩
  show VG p ((fwdDiff 1)^[k] P.eval 0) β
  rw [fwdDiff_iter_eq_sum_shift]
  apply VG.sum
  intro j hj
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  rw [zero_add, zsmul_eq_mul, nsmul_eq_mul, mul_one]
  have h1 : VG p (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) : ℤ) : ℚ) 0 := VG.intCast _
  have := h1.mul (hv j hjd)
  simpa using this

lemma VG_inv_24 : VG p ((24 : ℚ)⁻¹) (-(padicValNat p 24 : ℚ)) := by
  apply VG.inv (by norm_num)
  rw [show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  exact le_refl _

/-- **(3.9)**: `v_p(τ(P)) ≥ β - 4 ⌊log_p (d+1)⌋ - v_p(24)` if `deg P ≤ d` and
`v_p(P(m)) ≥ β` for `0 ≤ m ≤ d`. -/
theorem tau_bound {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) :
    VG p (tau P) (β - 4 * Nat.log p (d + 1) - padicValNat p 24) := by
  have h0 := binRep_of_values hd hv
  have hl : (Nat.log p d : ℚ) ≤ Nat.log p (d + 1) := by
    exact_mod_cast Nat.log_mono_right (Nat.le_succ d)
  have h3 : BinRep p d (β - 3 * Nat.log p (d + 1)) (derivative^[3] P) := by
    have := h0.derivative.derivative.derivative
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact this.mono (by linarith)
  have := h3.Lb.mul (VG_inv_24 (p := p))
  unfold tau
  rw [div_eq_mul_inv]
  exact this.mono (by linarith)

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

/-- **Window lemma**: values at `s, …, s + d` control the values at all integers. -/
theorem VG_eval_int_of_window {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) (s : ℤ) {β : ℚ}
    (hv : ∀ i ≤ d, VG p (P.eval ((s + i : ℤ) : ℚ)) β) (z : ℤ) : VG p (P.eval (z : ℚ)) β := by
  set Q := P.comp (X + C (s : ℚ)) with hQ
  have hQd : Q.natDegree ≤ d := by
    rw [hQ]
    refine (natDegree_comp_le).trans ?_
    have : (X + C (s : ℚ)).natDegree ≤ 1 := by
      rw [natDegree_X_add_C]
    calc P.natDegree * (X + C (s : ℚ)).natDegree ≤ d * 1 := Nat.mul_le_mul hd this
      _ = d := by ring
  have hQv : ∀ m ≤ d, VG p (Q.eval (m : ℚ)) β := by
    intro m hm
    have := hv m hm
    rw [hQ, eval_comp]
    simp only [eval_add, eval_X, eval_C]
    push_cast at this ⊢
    rwa [add_comm]
  obtain ⟨e, he, hev⟩ := binRep_of_values hQd hQv
  have hPz : P.eval (z : ℚ) = Q.eval ((z - s : ℤ) : ℚ) := by
    rw [hQ, eval_comp]; simp
  rw [hPz, he, eval_finsetSum]
  refine VG.sum _ fun m hm => ?_
  rw [eval_mul, eval_C]
  have := (hev m (by have := Finset.mem_range.mp hm; omega)).mul (VG_bin_eval_int (p := p) m (z - s))
  simpa using this

/-- **Kummer**: `v_p(C(n, k)⁻¹) ≥ -log_p n`. -/
lemma VG_choose_inv {n k : ℕ} (hk : k ≤ n) : VG p ((n.choose k : ℚ)⁻¹) (-(Nat.log p n : ℚ)) := by
  apply VG.inv (by exact_mod_cast (Nat.choose_pos hk).ne')
  rw [padicValRat.of_nat, ← Nat.factorization_def _ hp.out]
  exact_mod_cast Nat.factorization_choose_le_log

/-- `v_p(H^{(5)}_m) ≥ -5 log_p m`. -/
lemma VG_H5_log (m : ℕ) : VG p (H5 m) (-5 * (Nat.log p m : ℚ)) := by
  unfold H5
  refine VG.sum _ fun v hv => ?_
  have hv' := Finset.mem_Icc.mp hv
  have h := (VG.inv_nat (p := p) hv'.1 hv'.2).pow 5
  rw [inv_pow] at h
  rw [one_div]
  refine h.mono ?_
  push_cast; linarith

lemma log_mono {a b : ℕ} (h : a ≤ b) : (Nat.log p a : ℚ) ≤ Nat.log p b := by
  exact_mod_cast Nat.log_mono_right h

end Apery

end Port0

open Finset Polynomial in
/-- The platform target `Apery.VG_eval_int_of_window`, restated at top level as `solution`. -/
theorem solution {p : ℕ} [Fact p.Prime] {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) (s : ℤ) {β : ℚ}
    (hv : ∀ i ≤ d, Apery.VG p (P.eval ((s + i : ℤ) : ℚ)) β) (z : ℤ) :
    Apery.VG p (P.eval (z : ℚ)) β :=
  Apery.VG_eval_int_of_window (p := p) hd s hv z
