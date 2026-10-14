-- Prove2me | solution 1 for Apery.crude_tauX
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T19:24:47.257046+00:00
-- url     : https://prove2.me/submissions/a16b9b3c-d486-4b49-8495-59d28bc85bb0

/-
# The crude `τ_X` bound on the poles ±1,…,±K (source `Apery/Arith/SmallPrimeTau.lean`)

For $K \ge 1$, $2K \le d$ and $A \in \mathbb{Q}[X]$ of degree $\le d$ with
$p$-adically integral integer values, the functional $\tau_X$ on $(K!)^2 A$ with pole set
$\{ \pm 1, \dots, \pm K\}$ satisfies $v_p^G(\tau_X) \ge -6\log_p(d+1) - v_p(24)$.
The file ports the binomial basis and Bernoulli functional, the $\tau$-bound and `BinRep`, the
window lemma `VG_eval_int_of_window`, the residues and the product lemmas
(`prod_PlK`, `prod_erase_PlK`, `card_PlK`), and the theorem itself. Faithful port of
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourceValToolkit

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

lemma PlK_disjoint (K : ℕ) :
    Disjoint ((Icc 1 K).image (fun j : ℕ => (j : ℤ))) ((Icc 1 K).image (fun j : ℕ => -(j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, hab⟩ := h2
  rw [Finset.mem_Icc] at ha hb
  omega

lemma card_PlK (K : ℕ) : (PlK K).card = 2 * K := by
  rw [PlK, Finset.card_union_of_disjoint (PlK_disjoint K),
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp; ring

lemma prod_PlK {M : Type*} [CommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∏ r ∈ PlK K, f r = ∏ j ∈ Icc 1 K, (f j * f (-j)) := by
  rw [PlK, Finset.prod_union (PlK_disjoint K), Finset.prod_image (fun a _ b _ h => by exact_mod_cast h),
    Finset.prod_image (fun a _ b _ h => by simpa using h), Finset.prod_mul_distrib]

lemma dd_nat (j : ℕ) : dd (j : ℤ) = j := by simp [dd]

lemma dd_neg {j : ℕ} (hj : 1 ≤ j) : dd (-(j : ℤ)) = j - 1 := by
  unfold dd
  rw [if_neg (by omega)]
  omega


lemma prod_Icc_sub_mul_factorial (a : ℕ) : ∀ c : ℕ, c < a →
    (∏ i ∈ Icc 1 c, ((a : ℚ) - i)) * ((a - 1 - c).factorial : ℚ) = ((a - 1).factorial : ℚ) := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    rw [Finset.prod_Icc_succ_top (by omega), ← ih (by omega)]
    have e : a - 1 - c = (a - 1 - (c + 1)) + 1 := by omega
    rw [e, Nat.factorial_succ]
    push_cast [show c + 1 ≤ a by omega, show 1 ≤ a by omega]
    rw [show ((a - 1 - (c + 1) : ℕ) : ℚ) = (a : ℚ) - 1 - (c + 1) by
      push_cast [show c + 1 ≤ a - 1 by omega, show 1 ≤ a by omega]; ring]
    ring

lemma prod_Icc_add_mul_factorial (a c : ℕ) :
    (∏ i ∈ Icc 1 c, ((a : ℚ) + i)) * (a.factorial : ℚ) = ((a + c).factorial : ℚ) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.prod_Icc_succ_top (by omega), mul_right_comm, ih, ← add_assoc, Nat.factorial_succ]
    push_cast; ring

lemma prod_Ioc_sub (j t : ℕ) :
    ∏ i ∈ Ioc j (j + t), ((j : ℚ) - i) = (-1) ^ t * (t.factorial : ℚ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← add_assoc, Finset.prod_Ioc_succ_top (by omega), ih, Nat.factorial_succ, pow_succ]
    push_cast; ring

/-- `∏_{j ≤ K} (m - j) = K! C(m-1, K)` for `m > K`. -/
lemma prod_Icc_sub_eq_choose {m K : ℕ} (h : K < m) :
    ∏ j ∈ Icc 1 K, ((m : ℚ) - j) = (K.factorial : ℚ) * ((m - 1).choose K : ℚ) := by
  have h1 := prod_Icc_sub_mul_factorial m K h
  have h2 : ((m - 1).choose K : ℚ) * (K.factorial : ℚ) * ((m - 1 - K).factorial : ℚ) =
      ((m - 1).factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : K ≤ m - 1)
  have hne : ((m - 1 - K).factorial : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  rw [h1, ← h2]; ring

/-- `∏_{j ≤ K} (m + j) = K! C(m+K, K)`. -/
lemma prod_Icc_add_eq_choose (m K : ℕ) :
    ∏ j ∈ Icc 1 K, ((m : ℚ) + j) = (K.factorial : ℚ) * ((m + K).choose K : ℚ) := by
  have h1 := prod_Icc_add_mul_factorial m K
  have h2 : ((m + K).choose K : ℚ) * (K.factorial : ℚ) * (m.factorial : ℚ) =
      ((m + K).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : K ≤ m + K)
    rw [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hne : (m.factorial : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  rw [h1, ← h2]; ring

/-- The pole product at a point `m > K`. -/
lemma prod_PlK_sub {m K : ℕ} (h : K < m) :
    ∏ s ∈ PlK K, ((m : ℚ) - s) =
      (K.factorial : ℚ) ^ 2 * ((m - 1).choose K : ℚ) * ((m + K).choose K : ℚ) := by
  rw [prod_PlK, Finset.prod_mul_distrib]
  simp only [Int.cast_natCast, Int.cast_neg, sub_neg_eq_add]
  rw [prod_Icc_sub_eq_choose h, prod_Icc_add_eq_choose]; ring

/-- The product `∏_{i ≤ K, i ≠ j} (j - i)`. -/
lemma prod_Icc_ite_sub {j K : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ∏ i ∈ Icc 1 K, (if i = j then (1 : ℚ) else (j : ℚ) - i) =
      (-1) ^ (K - j) * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) := by
  have hsplit : Icc 1 K = Icc 1 j ∪ Ioc j K := by
    ext i; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 j) (Ioc j K) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  rw [hsplit, Finset.prod_union hdisj]
  have hA : ∏ i ∈ Icc 1 j, (if i = j then (1 : ℚ) else (j : ℚ) - i) = ((j - 1).factorial : ℚ) := by
    obtain ⟨c, rfl⟩ : ∃ c, j = c + 1 := ⟨j - 1, by omega⟩
    rw [Finset.prod_Icc_succ_top (by omega), if_pos rfl, mul_one]
    rw [Finset.prod_congr rfl (fun i hi => if_neg (by
      have := Finset.mem_Icc.mp hi; omega) : ∀ i ∈ Icc 1 c,
        (if i = c + 1 then (1 : ℚ) else ((c + 1 : ℕ) : ℚ) - i) = ((c + 1 : ℕ) : ℚ) - i)]
    have := prod_Icc_sub_mul_factorial (c + 1) c (by omega)
    rw [show c + 1 - 1 - c = 0 by omega, Nat.factorial_zero, Nat.cast_one, mul_one] at this
    rw [this]
  have hB : ∏ i ∈ Ioc j K, (if i = j then (1 : ℚ) else (j : ℚ) - i) =
      (-1) ^ (K - j) * ((K - j).factorial : ℚ) := by
    rw [Finset.prod_congr rfl (fun i hi => if_neg (by
      have := Finset.mem_Ioc.mp hi; omega) : ∀ i ∈ Ioc j K,
        (if i = j then (1 : ℚ) else (j : ℚ) - i) = (j : ℚ) - i)]
    have := prod_Ioc_sub j (K - j)
    rwa [show j + (K - j) = K by omega] at this
  rw [hA, hB]; ring

/-- Residue denominator at `r = ±j`, up to sign. -/
lemma prod_erase_PlK {j K : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ σ : ℚ, (σ = 1 ∨ σ = -1) ∧
      ∏ s ∈ (PlK K).erase (ε * j), (((ε * j : ℤ) : ℚ) - s) =
        σ * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) * ((K + j).factorial : ℚ) /
          (j.factorial : ℚ) := by
  classical
  set r : ℤ := ε * j with hr
  have hrmem : r ∈ PlK K := by
    rcases hε with rfl | rfl
    · simp only [hr, one_mul, PlK, Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjK⟩, rfl⟩
    · simp only [hr, neg_one_mul, PlK, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjK⟩, rfl⟩
  set f : ℤ → ℚ := fun s => if s = r then 1 else (r : ℚ) - s with hf
  have e1 : ∏ s ∈ (PlK K).erase r, ((r : ℚ) - s) = ∏ s ∈ PlK K, f s := by
    rw [← Finset.prod_erase_mul _ _ hrmem]
    simp only [hf, if_pos rfl, mul_one]
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [if_neg (Finset.mem_erase.mp hs).1]
  rw [e1, prod_PlK]
  have hPj := prod_Icc_ite_sub hj1 hjK
  have hjf : (j.factorial : ℚ) ≠ 0 := by positivity
  have hA' : ∏ i ∈ Icc 1 K, ((j : ℚ) + i) = ((K + j).factorial : ℚ) / (j.factorial : ℚ) := by
    rw [eq_div_iff hjf, prod_Icc_add_mul_factorial j K, add_comm]
  rcases hε with hε | hε
  · refine ⟨(-1) ^ (K - j), by rcases neg_one_pow_eq_or ℚ (K - j) with h | h <;> simp [h], ?_⟩
    have e2 : ∀ i ∈ Icc 1 K, f (i : ℤ) * f (-(i : ℤ)) =
        (if i = j then (1 : ℚ) else (j : ℚ) - i) * ((j : ℚ) + i) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      simp only [hf, hr, hε, one_mul]
      rw [if_neg (by omega : -(i : ℤ) ≠ (j : ℤ))]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (by exact_mod_cast hij), if_neg hij]; push_cast; ring
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, hPj, hA']
    ring
  · refine ⟨(-1) ^ (K - j) * (-1) ^ (2 * K - 1), ?_, ?_⟩
    · rcases neg_one_pow_eq_or ℚ (K - j) with h | h <;>
        rcases neg_one_pow_eq_or ℚ (2 * K - 1) with h' | h' <;> simp [h, h']
    have e2 : ∀ i ∈ Icc 1 K, f (i : ℤ) * f (-(i : ℤ)) =
        ((-1) * ((j : ℚ) + i)) * ((-1) * (if i = j then (-1 : ℚ) else (j : ℚ) - i)) := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      simp only [hf, hr, hε, neg_one_mul]
      rw [if_neg (by omega : (i : ℤ) ≠ -(j : ℤ))]
      by_cases hij : i = j
      · subst hij; simp; ring
      · rw [if_neg (by intro h; exact hij (by exact_mod_cast neg_injective h)), if_neg hij]
        push_cast; ring
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    have hPj' : ∏ i ∈ Icc 1 K, (if i = j then (-1 : ℚ) else (j : ℚ) - i) =
        -((-1) ^ (K - j) * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ)) := by
      rw [← hPj, ← Finset.mul_prod_erase _ _ (Finset.mem_Icc.mpr ⟨hj1, hjK⟩),
        ← Finset.mul_prod_erase (Icc 1 K) (fun i => if i = j then (1 : ℚ) else (j : ℚ) - i)
          (Finset.mem_Icc.mpr ⟨hj1, hjK⟩), if_pos rfl, if_pos rfl]
      rw [Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1]),
        Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1] :
          ∀ i ∈ (Icc 1 K).erase j, (if i = j then (1 : ℚ) else (j : ℚ) - i) = (j : ℚ) - i)]
      ring
    rw [hPj', hA']
    have h2K : (-1 : ℚ) ^ (2 * K - 1) * (-1) = 1 := by
      rw [← pow_succ, show 2 * K - 1 + 1 = 2 * K by omega, pow_mul]; norm_num
    have hodd : (-1 : ℚ) ^ (2 * K - 1) = -1 := by linear_combination (-1 : ℚ) * h2K
    have hK2 : (-1 : ℚ) ^ K * (-1) ^ K = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [hodd]
    linear_combination (-((-1 : ℚ) ^ (K - j) * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) *
      (((K + j).factorial : ℚ) / (j.factorial : ℚ)))) * hK2

lemma mem_PlK_iff {K : ℕ} {r : ℤ} (hr : r ∈ PlK K) :
    ∃ j ∈ Icc 1 K, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ r = ε * j := by
  simp only [PlK, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨j, hj, 1, Or.inl rfl, by ring⟩
  · exact ⟨j, hj, -1, Or.inr rfl, by ring⟩

/-- `(K!)² / ((K-j)! (K+j)!) = C(2K, K+j) / C(2K, K)`. -/
lemma factorial_ratio {j K : ℕ} (hjK : j ≤ K) :
    (K.factorial : ℚ) ^ 2 / (((K - j).factorial : ℚ) * ((K + j).factorial : ℚ)) =
      ((2 * K).choose (K + j) : ℚ) / ((2 * K).choose K : ℚ) := by
  have h1 : ((2 * K).choose (K + j) : ℚ) * ((K + j).factorial : ℚ) * ((K - j).factorial : ℚ) =
      ((2 * K).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : K + j ≤ 2 * K)
    rw [show 2 * K - (K + j) = K - j by omega] at this
    exact_mod_cast this
  have h2 : ((2 * K).choose K : ℚ) * (K.factorial : ℚ) * (K.factorial : ℚ) =
      ((2 * K).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : K ≤ 2 * K)
    rw [show 2 * K - K = K by omega] at this
    exact_mod_cast this
  have hc : ((2 * K).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have ha : ((K - j).factorial : ℚ) ≠ 0 := by positivity
  have hb : ((K + j).factorial : ℚ) ≠ 0 := by positivity
  rw [div_eq_div_iff (mul_ne_zero ha hb) hc]
  linear_combination h2 - h1

/-- The residue factor `(K!)² / ∏_{s ≠ r} (r - s)` has valuation `≥ -log_p (2K)`. -/
lemma VG_res_factor {K : ℕ} {r : ℤ} (hr : r ∈ PlK K) :
    VG p ((K.factorial : ℚ) ^ 2 / ∏ s ∈ (PlK K).erase r, ((r : ℚ) - s))
      (-(Nat.log p (2 * K) : ℚ)) := by
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  have hj' := Finset.mem_Icc.mp hj
  obtain ⟨σ, hσ, he⟩ := prod_erase_PlK hj'.1 hj'.2 ε hε
  rw [he]
  have hjf : (j.factorial : ℚ) = j * ((j - 1).factorial : ℚ) := by
    rw [← Nat.mul_factorial_pred (by omega : j ≠ 0)]; push_cast; ring
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have e : (K.factorial : ℚ) ^ 2 /
      (σ * ((j - 1).factorial : ℚ) * ((K - j).factorial : ℚ) * ((K + j).factorial : ℚ) /
        (j.factorial : ℚ)) =
      (σ * j) * (((2 * K).choose (K + j) : ℚ) * ((2 * K).choose K : ℚ)⁻¹) := by
    rw [← div_eq_mul_inv, ← factorial_ratio hj'.2, hjf]
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have h1 : ((j - 1).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((K - j).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((K + j).factorial : ℚ) ≠ 0 := by positivity
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
    linear_combination (-1 : ℚ) * hσ2
  rw [e]
  have hσv : VG p (σ * j) 0 := by
    rcases hσ with rfl | rfl
    · simpa using VG.natCast (p := p) j
    · simpa using (VG.natCast (p := p) j).neg
  have := hσv.mul ((VG.natCast (p := p) ((2 * K).choose (K + j))).mul
    (VG_choose_inv (p := p) (by omega : K ≤ 2 * K)))
  exact this.mono (by simp)

/-- **The analogue of Lemma 3.3** for the poles `±1, …, ±K`. -/
theorem crude_tauX {K d : ℕ} (hK : 1 ≤ K) (hdK : 2 * K ≤ d) (A : ℚ[X]) (hA : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) :
    GV p (tauX (C ((K.factorial : ℚ) ^ 2) * A) (PlK K))
      (-6 * (Nat.log p (d + 1) : ℚ) - padicValNat p 24) := by
  set g := C ((K.factorial : ℚ) ^ 2) * A with hg
  set Λ : ℚ := (Nat.log p (d + 1) : ℚ) with hΛ
  have hΛ0 : (0 : ℚ) ≤ Λ := by positivity
  have hlog2K : (Nat.log p (2 * K) : ℚ) ≤ Λ := log_mono (by omega)
  have hv24 : (0 : ℚ) ≤ padicValNat p 24 := by positivity
  -- residues
  have hres : ∀ r ∈ PlK K, VG p (resP g (PlK K) r) (-Λ) := by
    intro r hr
    unfold resP
    rw [hg, eval_mul, eval_C, mul_comm, mul_div_assoc]
    refine ((hint r).mul (VG_res_factor hr)).mono ?_
    linarith
  have hgdeg : g.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hA
  unfold tauX
  refine GV.add (GV.C ?_) (GV.sum _ fun r hr => ?_)
  · -- the polynomial part
    set P := polyPart g (PlK K) with hP
    have hPd : P.natDegree ≤ d - 2 * K := by
      have := natDegree_polyPart_le g (PlK K)
      rw [card_PlK, ← hP] at this
      omega
    -- values on the window
    have hwin : ∀ i ≤ d - 2 * K, VG p (P.eval ((((K + 1 : ℕ) : ℤ) + i : ℤ) : ℚ)) (-2 * Λ) := by
      intro i hi
      set m : ℕ := K + 1 + i with hm
      have hmK : K < m := by omega
      have hmd : m + K ≤ d + 1 := by omega
      have hcast : ((((K + 1 : ℕ) : ℤ) + i : ℤ) : ℚ) = (m : ℚ) := by rw [hm]; push_cast; ring
      rw [hcast]
      have hpf : g.eval (m : ℚ) = P.eval (m : ℚ) * (piPl (PlK K)).eval (m : ℚ) +
          ∑ r ∈ PlK K, (C (resP g (PlK K) r) * ∏ s ∈ (PlK K).erase r, (X - C (s : ℚ))).eval
            (m : ℚ) := by
        conv_lhs => rw [partial_fractionsP g (PlK K)]
        rw [eval_add, eval_mul, eval_finsetSum]
      have hpi : (piPl (PlK K)).eval (m : ℚ) = ∏ s ∈ PlK K, ((m : ℚ) - s) := by
        unfold piPl; rw [eval_prod]; simp
      have hpi' := prod_PlK_sub (K := K) hmK
      have hne : ∀ s ∈ PlK K, (m : ℚ) - s ≠ 0 := by
        intro s hs
        obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hs
        have := (Finset.mem_Icc.mp hj).2
        rcases hε with rfl | rfl <;> push_cast <;> intro h
        · have : (m : ℚ) = j := by linarith
          have : m = j := by exact_mod_cast this
          omega
        · have : (m : ℚ) + j = 0 := by linarith
          have : m + j = 0 := by exact_mod_cast this
          omega
      have hPi0 : ∏ s ∈ PlK K, ((m : ℚ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
      have hterm : ∀ r ∈ PlK K, (C (resP g (PlK K) r) * ∏ s ∈ (PlK K).erase r, (X - C (s : ℚ))).eval
          (m : ℚ) = resP g (PlK K) r / ((m : ℚ) - r) * ∏ s ∈ PlK K, ((m : ℚ) - s) := by
        intro r hr
        rw [eval_mul, eval_C, eval_prod, ← Finset.mul_prod_erase _ _ hr]
        simp only [eval_sub, eval_X, eval_C]
        field_simp [hne r hr]
      rw [Finset.sum_congr rfl hterm, hpi, ← Finset.sum_mul] at hpf
      have hPm : P.eval (m : ℚ) = g.eval (m : ℚ) / ∏ s ∈ PlK K, ((m : ℚ) - s) -
          ∑ r ∈ PlK K, resP g (PlK K) r / ((m : ℚ) - r) := by
        rw [eq_sub_iff_add_eq, eq_div_iff hPi0, add_mul]
        exact hpf.symm
      rw [hPm]
      refine VG.sub ?_ (VG.sum _ fun r hr => ?_)
      · rw [hpi', hg, eval_mul, eval_C]
        have hc1 : ((m - 1).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
        have hc2 : ((m + K).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
        have hKf : (K.factorial : ℚ) ≠ 0 := by positivity
        have e : (K.factorial : ℚ) ^ 2 * A.eval (m : ℚ) /
            ((K.factorial : ℚ) ^ 2 * ((m - 1).choose K : ℚ) * ((m + K).choose K : ℚ)) =
            A.eval (m : ℚ) * (((m - 1).choose K : ℚ)⁻¹ * ((m + K).choose K : ℚ)⁻¹) := by
          field_simp
        rw [e]
        have h1 := VG_choose_inv (p := p) (by omega : K ≤ m - 1)
        have h2 := VG_choose_inv (p := p) (by omega : K ≤ m + K)
        have l1 : (Nat.log p (m - 1) : ℚ) ≤ Λ := log_mono (by omega)
        have l2 : (Nat.log p (m + K) : ℚ) ≤ Λ := log_mono (by omega)
        have := (hint m).mul (h1.mul h2)
        push_cast at this
        exact this.mono (by linarith)
      · obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
        have hj' := Finset.mem_Icc.mp hj
        have hpos : ∃ u : ℕ, 1 ≤ u ∧ u ≤ d + 1 ∧ (m : ℚ) - ((ε * j : ℤ) : ℚ) = u := by
          rcases hε with rfl | rfl
          · exact ⟨m - j, by omega, by omega, by push_cast [show j ≤ m by omega]; ring⟩
          · exact ⟨m + j, by omega, by omega, by push_cast; ring⟩
        obtain ⟨u, hu1, hud, hu⟩ := hpos
        rw [div_eq_mul_inv, hu]
        have := (hres _ hr).mul (VG.inv_nat (p := p) hu1 hud)
        exact this.mono (by rw [← hΛ]; linarith)
    have hall := VG_eval_int_of_window hPd ((K + 1 : ℕ) : ℤ) hwin
    have htau := tau_bound (p := p) hPd (β := -2 * Λ) (fun m _ => by
      have := hall m; simpa using this)
    refine htau.mono ?_
    have : (Nat.log p (d - 2 * K + 1) : ℚ) ≤ Λ := log_mono (by omega)
    linarith
  · -- the pole terms
    obtain ⟨j, hj, ε, hε, hrj⟩ := mem_PlK_iff hr
    have hj' := Finset.mem_Icc.mp hj
    have hdd : dd r ≤ d + 1 := by
      rw [hrj]; rcases hε with rfl | rfl
      · rw [one_mul, dd_nat]; omega
      · rw [neg_one_mul, dd_neg hj'.1]; omega
    have hH : GV p (C (H5 (dd r)) - X) (-5 * Λ) :=
      (GV.C ((VG_H5_log (p := p) (dd r)).mono (by
        have : (Nat.log p (dd r) : ℚ) ≤ Λ := log_mono hdd
        linarith))).sub (GV.X.mono (by linarith))
    refine (GV.C_mul (hres r hr) hH).mono ?_
    linarith

end Apery

end Port0

open Finset Polynomial in
/-- The platform target `Apery.crude_tauX`, restated at top level as `solution`. -/
theorem solution {p : ℕ} [Fact p.Prime] {K d : ℕ} (hK : 1 ≤ K) (hdK : 2 * K ≤ d) (A : ℚ[X])
    (hA : A.natDegree ≤ d) (hint : ∀ z : ℤ, Apery.VG p (A.eval (z : ℚ)) 0) :
    Apery.GV p (Apery.tauX (Polynomial.C ((K.factorial : ℚ) ^ 2) * A) (Apery.PlK K))
      (-6 * (Nat.log p (d + 1) : ℚ) - padicValNat p 24) :=
  Apery.crude_tauX hK hdK A hA hint
