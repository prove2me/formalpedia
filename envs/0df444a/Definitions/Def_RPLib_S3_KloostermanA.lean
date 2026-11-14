-- Prove2me | Definitions.Def_RPLib_S3_KloostermanA
-- name    : RPLib_S3_KloostermanA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T23:24:38.277318+00:00
-- url     : https://prove2.me/theorems/2e79186f-4de3-4cfd-8513-c2c446ea2aa4
-- title:
--   Kloosterman sums: the fourth moment and Kloosterman's bound modulo a prime
-- statement:
--   Kloosterman sums
--
--   $$S(m,r;N) = \sum_{x \in (\mathbb Z/N\mathbb Z)^\times} e\!\left(\frac{m x + r \bar x}{N}\right), \qquad e(t) = e^{2\pi i t},$$
--
--   where $\bar x$ is the inverse of $x$ modulo $N$ (`kl N m r`, written with `ZMod.stdAddChar`). For every $N \ge 1$ the file proves the trivial bound $|S(m,r;N)| \le \varphi(N)$ and the symmetries $S(um,r;N) = S(m,ur;N)$ for units $u$ and $S(m,r;N) = S(r,m;N)$. For a prime $p$ it proves $S(m,0;p) = S(0,r;p) = -1$ for $m, r \ne 0$, the fourth moment
--
--   $$\sum_{m, r \in \mathbb F_p} |S(m,r;p)|^4 \le 3p^2(p-1)^2,$$
--
--   Kloosterman's bound $|S(m,r;p)|^4 \le 3p^3$ for $m, r \ne 0$, and its consequence $|S(m,r;p)| \le p^{7/8}$ for $p \ge 9$ and $(m,r) \ne (0,0)$.
--
--   **Formalization note.** This file is a library module (namespace `RamanujanPetersson.KL`) of a formalization of the Ramanujan-Petersson conjecture. It contains one definition (`kl`), proved lemmas only (no `sorry`), and a global instance `NeZero p` derived from `Fact p.Prime`, so that later solution files can import them. It imports Mathlib only.
-- source:
--   H. D. Kloosterman, On the representation of numbers in the form ax^2 + by^2 + cz^2 + dt^2, Acta Mathematica 49 (1926), 407-464; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapter 11

import Mathlib

/-!
# S3-ES-Wt2 (O4, KL_A): Kloosterman sums, the fourth moment and Kloosterman's bound mod p

`kl N m r = Σ_{x ∈ (ℤ/N)ˣ} e((m x + r x⁻¹)/N)` (with `ZMod.stdAddChar`).
* general `N`: `norm_kl_le` (trivial bound `φ(N)`), `kl_unit_mul`, `kl_comm`;
* `N = p` prime: `kl_zero_right`, `kl_zero_left` (`= -1`), the Parseval identity `sum_norm_sq_charSum`,
  the fourth moment `sum_norm_kl_pow_four_le` (`Σ_{m,r} |S|^4 ≤ 3 p^2 (p-1)^2`),
  Kloosterman's bound `norm_kl_pow_four_le` (`|S(m,r;p)|^4 ≤ 3 p^3` for `m, r ≠ 0`) and
  `norm_kl_pow_eight_le`, `norm_kl_le_rpow` (`|S(m,r;p)| ≤ p^(7/8)` for `p ≥ 9`, `(m,r) ≠ (0,0)`).
-/

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KL

/-- The Kloosterman sum `S(m, r; N) = Σ_{x ∈ (ℤ/N)ˣ} e((m x + r x⁻¹)/N)`. -/
def kl (N : ℕ) [NeZero N] (m r : ZMod N) : ℂ :=
  ∑ x : (ZMod N)ˣ, ZMod.stdAddChar (m * (x : ZMod N) + r * (x : ZMod N)⁻¹)

lemma norm_stdAddChar (N : ℕ) [NeZero N] (t : ZMod N) : ‖(ZMod.stdAddChar t : ℂ)‖ = 1 :=
  AddChar.norm_apply _ _

lemma norm_kl_le (N : ℕ) [NeZero N] (m r : ZMod N) : ‖kl N m r‖ ≤ Fintype.card (ZMod N)ˣ := by
  unfold kl
  refine (norm_sum_le _ _).trans ?_
  simp

lemma kl_unit_mul (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (m r : ZMod N) :
    kl N ((u : ZMod N) * m) r = kl N m ((u : ZMod N) * r) := by
  unfold kl
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun x => ?_)
  congr 1
  simp only [Equiv.coe_mulLeft]
  simp only [ZMod.inv_coe_unit]
  simp only [mul_inv_rev, Units.val_mul]
  have hU : (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv u
  linear_combination (-(r * ((x⁻¹ : (ZMod N)ˣ) : ZMod N))) * hU

lemma kl_comm (N : ℕ) [NeZero N] (m r : ZMod N) : kl N m r = kl N r m := by
  unfold kl
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun x => ?_)
  congr 1
  simp only [Equiv.inv_apply, ZMod.inv_coe_unit, inv_inv]
  ring

/-! ### Prime modulus -/

variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

lemma sum_stdAddChar_mul (A : ZMod p) :
    ∑ m : ZMod p, (ZMod.stdAddChar (m * A) : ℂ) = if A = 0 then (p : ℂ) else 0 := by
  rw [AddChar.sum_mulShift A (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  split_ifs <;> simp

lemma sum_units_eq {M : Type*} [AddCommGroup M] (f : ZMod p → M) :
    ∑ x : (ZMod p)ˣ, f x = ∑ y : ZMod p, f y - f 0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), add_sub_cancel_right]
  refine Finset.sum_bij (fun x _ => (x : ZMod p)) (fun x _ => ?_) (fun x _ y _ h => Units.ext h)
    (fun y hy => ⟨Units.mk0 y (Finset.ne_of_mem_erase hy), Finset.mem_univ _, rfl⟩) (fun x _ => rfl)
  exact Finset.mem_erase.2 ⟨x.ne_zero, Finset.mem_univ _⟩

lemma kl_zero_right {m : ZMod p} (hm : m ≠ 0) : kl p m 0 = -1 := by
  unfold kl
  simp only [zero_mul, add_zero]
  rw [sum_units_eq (fun y : ZMod p => (ZMod.stdAddChar (m * y) : ℂ))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  have h := sum_stdAddChar_mul (p := p) m
  simp only [hm, if_false] at h
  rw [show (∑ y : ZMod p, (ZMod.stdAddChar (m * y) : ℂ)) = ∑ y : ZMod p, ZMod.stdAddChar (y * m) from
    Finset.sum_congr rfl (fun y _ => by rw [mul_comm]), h, zero_sub]

lemma kl_zero_left {r : ZMod p} (hr : r ≠ 0) : kl p 0 r = -1 := by
  rw [kl_comm]; exact kl_zero_right hr

lemma kl_zero_zero : kl p 0 0 = ((p : ℂ) - 1) := by
  unfold kl
  simp only [zero_mul, add_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    ZMod.card_units, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]

lemma norm_kl_le_pred (m r : ZMod p) : ‖kl p m r‖ ≤ (p : ℝ) - 1 := by
  have h := norm_kl_le p m r
  rwa [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] at h

/-- Parseval in two variables: `Σ_{m,r} |Σ_v e((m s v + r t v)/p)|^2 = p^2 #{(v,w) : s v = s w, t v = t w}`. -/
lemma sum_norm_sq_charSum {V : Type*} [Fintype V] (s t : V → ZMod p) :
    ∑ m : ZMod p, ∑ r : ZMod p, ‖∑ v, (ZMod.stdAddChar (m * s v + r * t v) : ℂ)‖ ^ 2 =
      (p : ℝ) ^ 2 * (#{vw : V × V | s vw.1 = s vw.2 ∧ t vw.1 = t vw.2} : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ m r : ZMod p, ((‖∑ v, (ZMod.stdAddChar (m * s v + r * t v) : ℂ)‖ : ℝ) : ℂ) ^ 2 =
      ∑ v, ∑ w, (ZMod.stdAddChar (m * (s v - s w)) : ℂ) * ZMod.stdAddChar (r * (t v - t w)) := by
    intro m r
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1; ring
  simp_rw [key]
  have h2 : ∀ v w : V, (∑ m : ZMod p, ∑ r : ZMod p,
      (ZMod.stdAddChar (m * (s v - s w)) : ℂ) * ZMod.stdAddChar (r * (t v - t w))) =
      (p : ℂ) ^ 2 * (if s v = s w ∧ t v = t w then 1 else 0) := by
    intro v w
    rw [← Finset.sum_mul_sum, sum_stdAddChar_mul, sum_stdAddChar_mul]
    by_cases h1 : s v = s w <;> by_cases h2 : t v = t w <;> simp [h1, h2, sub_eq_zero, sq]
  calc ∑ m : ZMod p, ∑ r : ZMod p, ∑ v, ∑ w,
        (ZMod.stdAddChar (m * (s v - s w)) : ℂ) * ZMod.stdAddChar (r * (t v - t w))
      = ∑ m : ZMod p, ∑ v, ∑ w, ∑ r : ZMod p,
        (ZMod.stdAddChar (m * (s v - s w)) : ℂ) * ZMod.stdAddChar (r * (t v - t w)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun v _ => Finset.sum_comm)
    _ = ∑ v, ∑ w, ∑ m : ZMod p, ∑ r : ZMod p,
        (ZMod.stdAddChar (m * (s v - s w)) : ℂ) * ZMod.stdAddChar (r * (t v - t w)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun v _ => Finset.sum_comm)
    _ = ∑ v, ∑ w, (p : ℂ) ^ 2 * (if s v = s w ∧ t v = t w then 1 else 0) := by
        simp_rw [h2]
    _ = (p : ℂ) ^ 2 * (#{vw : V × V | s vw.1 = s vw.2 ∧ t vw.1 = t vw.2} : ℂ) := by
        simp_rw [← Finset.mul_sum]
        rw [← Fintype.sum_prod_type' (f := fun v w => if s v = s w ∧ t v = t w then (1 : ℂ) else 0),
          Finset.sum_boole]

/-- `S(m,r)^2 = Σ_{(x,y)} e((m (x + y) + r (x⁻¹ + y⁻¹))/p)`. -/
lemma kl_sq (m r : ZMod p) : kl p m r ^ 2 = ∑ v : (ZMod p)ˣ × (ZMod p)ˣ,
    (ZMod.stdAddChar (m * ((v.1 : ZMod p) + (v.2 : ZMod p)) + r * ((v.1 : ZMod p)⁻¹ + (v.2 : ZMod p)⁻¹)) : ℂ) := by
  rw [sq, kl, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [← AddChar.map_add_eq_mul]; congr 1; ring

lemma pair_eq_of {a b c d : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hs : a + b ≠ 0) (h1 : c + d = a + b) (h2 : c⁻¹ + d⁻¹ = a⁻¹ + b⁻¹) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  rw [inv_add_inv hc hd, inv_add_inv ha hb, h1,
    div_eq_div_iff (mul_ne_zero hc hd) (mul_ne_zero ha hb)] at h2
  have hcd : a * b = c * d := mul_left_cancel₀ hs h2
  have hq : (c - a) * (c - b) = 0 := by linear_combination c * h1 + hcd
  rcases mul_eq_zero.1 hq with h | h
  · left; refine ⟨sub_eq_zero.1 h, ?_⟩; linear_combination h1 - h
  · right; refine ⟨sub_eq_zero.1 h, ?_⟩; linear_combination h1 - h

lemma card_sum_zero_le : #{v : (ZMod p)ˣ × (ZMod p)ˣ | (v.1 : ZMod p) + (v.2 : ZMod p) = 0} ≤ p - 1 := by
  calc #{v : (ZMod p)ˣ × (ZMod p)ˣ | (v.1 : ZMod p) + (v.2 : ZMod p) = 0}
      ≤ (Finset.univ : Finset (ZMod p)ˣ).card := by
        refine Finset.card_le_card_of_injOn Prod.fst (by intro v _; exact Finset.mem_univ _) ?_
        intro v hv w hw h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
        refine Prod.ext h (Units.ext ?_)
        have h' : (v.1 : ZMod p) = w.1 := by rw [h]
        linear_combination hv - hw - h'
    _ = p - 1 := by rw [Finset.card_univ, ZMod.card_units]

lemma card_fiber_le (v : (ZMod p)ˣ × (ZMod p)ˣ) :
    #{w : (ZMod p)ˣ × (ZMod p)ˣ | (v.1 : ZMod p) + (v.2 : ZMod p) = (w.1 : ZMod p) + (w.2 : ZMod p) ∧
      (v.1 : ZMod p)⁻¹ + (v.2 : ZMod p)⁻¹ = (w.1 : ZMod p)⁻¹ + (w.2 : ZMod p)⁻¹} ≤
      if (v.1 : ZMod p) + (v.2 : ZMod p) = 0 then p - 1 else 2 := by
  split_ifs with h0
  · refine le_trans (Finset.card_le_card ?_) card_sum_zero_le
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [← hw.1, h0]
  · refine le_trans (Finset.card_le_card (t := {v, (v.2, v.1)}) ?_) Finset.card_le_two
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases pair_eq_of v.1.ne_zero v.2.ne_zero w.1.ne_zero w.2.ne_zero h0 hw.1.symm hw.2.symm with
      ⟨e1, e2⟩ | ⟨e1, e2⟩
    · simp [Prod.ext_iff, Units.ext e1, Units.ext e2]
    · simp [Prod.ext_iff, Units.ext e1, Units.ext e2]

lemma card_quad_le :
    #{vw : ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) |
      (vw.1.1 : ZMod p) + (vw.1.2 : ZMod p) = (vw.2.1 : ZMod p) + (vw.2.2 : ZMod p) ∧
      (vw.1.1 : ZMod p)⁻¹ + (vw.1.2 : ZMod p)⁻¹ = (vw.2.1 : ZMod p)⁻¹ + (vw.2.2 : ZMod p)⁻¹} ≤
      3 * (p - 1) ^ 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [← Finset.card_filter]
  calc ∑ v : (ZMod p)ˣ × (ZMod p)ˣ, #{w : (ZMod p)ˣ × (ZMod p)ˣ |
          (v.1 : ZMod p) + (v.2 : ZMod p) = (w.1 : ZMod p) + (w.2 : ZMod p) ∧
          (v.1 : ZMod p)⁻¹ + (v.2 : ZMod p)⁻¹ = (w.1 : ZMod p)⁻¹ + (w.2 : ZMod p)⁻¹}
      ≤ ∑ v : (ZMod p)ˣ × (ZMod p)ˣ, ((if (v.1 : ZMod p) + (v.2 : ZMod p) = 0 then p - 1 else 0) + 2) := by
        refine Finset.sum_le_sum (fun v _ => (card_fiber_le v).trans ?_)
        split_ifs <;> omega
    _ = #{v : (ZMod p)ˣ × (ZMod p)ˣ | (v.1 : ZMod p) + (v.2 : ZMod p) = 0} * (p - 1) + 2 * (p - 1) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, Fintype.card_prod, ZMod.card_units, smul_eq_mul, smul_eq_mul]
        ring
    _ ≤ (p - 1) * (p - 1) + 2 * (p - 1) ^ 2 := by
        gcongr; exact card_sum_zero_le
    _ = 3 * (p - 1) ^ 2 := by ring

/-- Fourth moment: `Σ_{m,r} |S(m,r;p)|^4 ≤ 3 p^2 (p-1)^2`. -/
lemma sum_norm_kl_pow_four_le :
    ∑ m : ZMod p, ∑ r : ZMod p, ‖kl p m r‖ ^ 4 ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 := by
  have e : ∀ m r : ZMod p, ‖kl p m r‖ ^ 4 = ‖kl p m r ^ 2‖ ^ 2 := fun m r => by rw [norm_pow]; ring
  simp_rw [e, kl_sq]
  have hP := sum_norm_sq_charSum (p := p) (fun v : (ZMod p)ˣ × (ZMod p)ˣ => (v.1 : ZMod p) + (v.2 : ZMod p))
    (fun v => (v.1 : ZMod p)⁻¹ + (v.2 : ZMod p)⁻¹)
  beta_reduce at hP
  rw [hP]
  have hc : (#{vw : ((ZMod p)ˣ × (ZMod p)ˣ) × ((ZMod p)ˣ × (ZMod p)ˣ) |
      (vw.1.1 : ZMod p) + (vw.1.2 : ZMod p) = (vw.2.1 : ZMod p) + (vw.2.2 : ZMod p) ∧
      (vw.1.1 : ZMod p)⁻¹ + (vw.1.2 : ZMod p)⁻¹ = (vw.2.1 : ZMod p)⁻¹ + (vw.2.2 : ZMod p)⁻¹} : ℝ) ≤
      3 * ((p : ℝ) - 1) ^ 2 := by
    have h := card_quad_le (p := p)
    have h' : ((3 * (p - 1) ^ 2 : ℕ) : ℝ) = 3 * ((p : ℝ) - 1) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (Fact.out : p.Prime).one_le]; norm_num
    rw [← h']; exact_mod_cast h
  have hp2 : (0 : ℝ) ≤ (p : ℝ) ^ 2 := by positivity
  calc (p : ℝ) ^ 2 * _ ≤ (p : ℝ) ^ 2 * (3 * ((p : ℝ) - 1) ^ 2) := mul_le_mul_of_nonneg_left hc hp2
    _ = 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 := by ring

lemma kl_unit_div (u : (ZMod p)ˣ) (a : ZMod p) : kl p u (a * (u : ZMod p)⁻¹) = kl p 1 a := by
  have h := kl_unit_mul p u 1 (a * (u : ZMod p)⁻¹)
  rw [mul_one] at h
  rw [h]; congr 1
  rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ u.ne_zero, one_mul]

lemma norm_kl_one_pow_four_le {a : ZMod p} (ha : a ≠ 0) : ‖kl p 1 a‖ ^ 4 ≤ 3 * (p : ℝ) ^ 3 := by
  have _ha := ha
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have key : ((p : ℝ) - 1) * ‖kl p 1 a‖ ^ 4 ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 := by
    calc ((p : ℝ) - 1) * ‖kl p 1 a‖ ^ 4 = ∑ u : (ZMod p)ˣ, ‖kl p u (a * (u : ZMod p)⁻¹)‖ ^ 4 := by
          simp only [kl_unit_div, Finset.sum_const, Finset.card_univ, ZMod.card_units, nsmul_eq_mul]
          rw [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
      _ ≤ ∑ u : (ZMod p)ˣ, ∑ r : ZMod p, ‖kl p u r‖ ^ 4 :=
          Finset.sum_le_sum (fun u _ => Finset.single_le_sum (f := fun r => ‖kl p u r‖ ^ 4)
            (fun r _ => by positivity) (Finset.mem_univ _))
      _ ≤ ∑ m : ZMod p, ∑ r : ZMod p, ‖kl p m r‖ ^ 4 := by
          rw [sum_units_eq (fun m : ZMod p => ∑ r : ZMod p, ‖kl p m r‖ ^ 4)]
          have : 0 ≤ ∑ r : ZMod p, ‖kl p 0 r‖ ^ 4 := Finset.sum_nonneg (fun r _ => by positivity)
          linarith
      _ ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 := sum_norm_kl_pow_four_le
  have hpos : 0 < (p : ℝ) - 1 := by linarith
  have h2 : ‖kl p 1 a‖ ^ 4 ≤ 3 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith [key]
  have : 0 ≤ 3 * (p : ℝ) ^ 2 := by positivity
  linarith

/-- Kloosterman's bound: `|S(m, r; p)|^4 ≤ 3 p^3` for `m, r ≠ 0`. -/
theorem norm_kl_pow_four_le {m r : ZMod p} (hm : m ≠ 0) (hr : r ≠ 0) :
    ‖kl p m r‖ ^ 4 ≤ 3 * (p : ℝ) ^ 3 := by
  have h := kl_unit_mul p (Units.mk0 m hm) 1 r
  rw [Units.val_mk0, mul_one] at h
  rw [h]; exact norm_kl_one_pow_four_le (mul_ne_zero hm hr)

/-- `|S(m, r; p)|^8 ≤ p^7` for `p ≥ 9` and `(m, r) ≠ (0, 0)`. -/
theorem norm_kl_pow_eight_le (hp : 9 ≤ p) {m r : ZMod p} (h : m ≠ 0 ∨ r ≠ 0) :
    ‖kl p m r‖ ^ 8 ≤ (p : ℝ) ^ 7 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp9 : (9 : ℝ) ≤ p := by exact_mod_cast hp
  have one_le : (1 : ℝ) ≤ (p : ℝ) ^ 7 := one_le_pow₀ hp1
  by_cases hm : m = 0
  · have hr : r ≠ 0 := h.resolve_left (not_not.2 hm)
    rw [hm, kl_zero_left hr]; simpa using one_le
  by_cases hr : r = 0
  · rw [hr, kl_zero_right hm]; simpa using one_le
  have h4 := norm_kl_pow_four_le hm hr
  have h0 : 0 ≤ ‖kl p m r‖ ^ 4 := by positivity
  calc ‖kl p m r‖ ^ 8 = (‖kl p m r‖ ^ 4) ^ 2 := by ring
    _ ≤ (3 * (p : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ h0 h4 2
    _ = 9 * (p : ℝ) ^ 6 := by ring
    _ ≤ (p : ℝ) * (p : ℝ) ^ 6 := by gcongr
    _ = (p : ℝ) ^ 7 := by ring

/-- `|S(m, r; p)| ≤ p^(7/8)` for `p ≥ 9` and `(m, r) ≠ (0, 0)`. -/
theorem norm_kl_le_rpow (hp : 9 ≤ p) {m r : ZMod p} (h : m ≠ 0 ∨ r ≠ 0) :
    ‖kl p m r‖ ≤ (p : ℝ) ^ ((7 : ℝ) / 8) := by
  have h8 := norm_kl_pow_eight_le hp h
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by norm_num : (8 : ℕ) ≠ 0)]
  have e : ((p : ℝ) ^ ((7 : ℝ) / 8)) ^ (8 : ℕ) = (p : ℝ) ^ (7 : ℕ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ ((7 : ℝ) / 8)) 8, ← Real.rpow_mul hp0, ← Real.rpow_natCast]
    norm_num
  rw [e]; exact h8

end RamanujanPetersson.KL


