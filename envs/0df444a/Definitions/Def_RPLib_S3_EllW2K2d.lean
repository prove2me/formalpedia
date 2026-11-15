-- Prove2me | Definitions.Def_RPLib_S3_EllW2K2d
-- name    : RPLib_S3_EllW2K2d
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:55:44.903+00:00
-- url     : https://prove2.me/theorems/225cc452-a409-4c81-ac59-c29b43a1b96f
-- title:
--   The Eichler-Selberg trace formula in weight two: the crude count of the `A0 M`-part
-- statement:
--   The crude count of the `A0 M`-part.
--
--   * `sum_zmod_val'`, `sum_range_mul_of_periodic'`: generic versions (any coefficient ring).
--   * `card_row_eq`: `#{x mod A0 M : A0 ∣ x(t-x) - n} = M · #{a < A0 : A0 ∣ a(t-a) - n}`.
--   * **`card_PA_le`**: `#{(x, y) mod A0 M : A0 ∣ x(y-x) - n} ≤ 2 M² A0^(7/4)` (from EX `card_fib_le_rpow`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K2c

/-!
# S3-ES-Wt2 (O6, file K2d): the crude count of the `A0 M`-part

* `sum_zmod_val'`, `sum_range_mul_of_periodic'`: generic versions (any coefficient ring).
* `card_row_eq`: `#{x mod A0 M : A0 ∣ x(t-x) - n} = M · #{a < A0 : A0 ∣ a(t-a) - n}`.
* **`card_PA_le`**: `#{(x, y) mod A0 M : A0 ∣ x(y-x) - n} ≤ 2 M² A0^(7/4)` (from EX `card_fib_le_rpow`).
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

lemma sum_zmod_val' {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (h : ℕ → R) :
    ∑ x : ZMod q, h x.val = ∑ u ∈ range q, h u := by
  refine Finset.sum_bij' (fun x _ => x.val) (fun u _ => (u : ZMod q))
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun u _ => Finset.mem_univ _)
    (fun x _ => ZMod.natCast_zmod_val x) (fun u hu => ZMod.val_natCast_of_lt (Finset.mem_range.mp hu))
    (fun x _ => rfl)

lemma sum_range_mul_of_periodic' {R : Type*} [CommSemiring R] {G : ℕ → R} {C : ℕ}
    (hG : ∀ a, G (a + C) = G a) (K : ℕ) :
    ∑ a ∈ range (C * K), G a = K * ∑ a ∈ range C, G a := by
  have hGk : ∀ k a, G (C * k + a) = G a := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih => intro a; rw [show C * (k + 1) + a = (C * k + a) + C by ring, hG, ih]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show C * (K + 1) = C * K + C by ring, Finset.sum_range_add, ih]
    simp only [hGk]; push_cast; ring

lemma card_row_eq (M : ℕ) [NeZero M] (n t : ℤ) {A0 : ℕ} [NeZero A0] :
    (univ.filter fun x : ZMod (A0 * M) => (A0 : ℤ) ∣ (x.val : ℤ) * (t - x.val) - n).card =
      M * ((range A0).filter fun a : ℕ => (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n).card := by
  have hG : ∀ a : ℕ,
      (if (A0 : ℤ) ∣ ((a + A0 : ℕ) : ℤ) * (t - ((a + A0 : ℕ) : ℤ)) - n then 1 else 0 : ℕ) =
        (if (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n then 1 else 0 : ℕ) := by
    intro a
    have hd : (A0 : ℤ) ∣ ((a + A0 : ℕ) : ℤ) * (t - ((a + A0 : ℕ) : ℤ)) - n ↔
        (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n := by
      rw [show ((a + A0 : ℕ) : ℤ) * (t - ((a + A0 : ℕ) : ℤ)) - n =
        (a : ℤ) * (t - a) - n + (A0 : ℤ) * (t - 2 * a - A0) by push_cast; ring]
      exact dvd_add_left (dvd_mul_right _ _)
    by_cases h : (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n
    · rw [if_pos (hd.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hd.1 h')), if_neg h]
  rw [Finset.card_filter, Finset.card_filter,
    sum_zmod_val' (q := A0 * M) (fun a : ℕ => if (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n then 1 else 0),
    sum_range_mul_of_periodic' hG M]
  simp

lemma card_row_le (M : ℕ) [NeZero M] (n t : ℤ) {A0 : ℕ} [NeZero A0] :
    ((univ.filter fun x : ZMod (A0 * M) => (A0 : ℤ) ∣ (x.val : ℤ) * (t - x.val) - n).card : ℝ) ≤
      M * (2 * (A0 : ℝ) ^ ((3 : ℝ) / 4)) := by
  rw [card_row_eq M n t, Nat.cast_mul]
  have hA : (A0 : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne A0
  have h1 := card_fib_le_rpow n hA t
  rw [Int.natAbs_natCast] at h1
  have h2 : ((range A0).filter fun a : ℕ => (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n).card ≤
      (fib n (A0 : ℤ) t).card := by
    refine Finset.card_le_card_of_injOn (fun a : ℕ => (a : ℤ)) ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
      simp only [fib, Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq, Nat.abs_cast]
      exact ⟨⟨Int.natCast_nonneg a, by exact_mod_cast ha.1⟩, ha.2⟩
    · intro a _ b _ h
      exact Int.natCast_inj.1 h
  have h3 : (((range A0).filter fun a : ℕ => (A0 : ℤ) ∣ (a : ℤ) * (t - a) - n).card : ℝ) ≤
      2 * (A0 : ℝ) ^ ((3 : ℝ) / 4) := by
    refine le_trans (Nat.cast_le.2 h2) ?_
    convert h1 using 3
  exact mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg M)

/-- **The crude count** `#PA ≤ 2 M² A0^(7/4)`. -/
theorem card_PA_le (M : ℕ) [NeZero M] (n : ℤ) {A0 : ℕ} [NeZero A0] :
    ((univ.filter fun p : ZMod (A0 * M) × ZMod (A0 * M) =>
        (A0 : ℤ) ∣ (p.1.val : ℤ) * ((p.2.val : ℤ) - p.1.val) - n).card : ℝ) ≤
      2 * (M : ℝ) ^ 2 * (A0 : ℝ) ^ ((7 : ℝ) / 4) := by
  have hsplit : (univ.filter fun p : ZMod (A0 * M) × ZMod (A0 * M) =>
        (A0 : ℤ) ∣ (p.1.val : ℤ) * ((p.2.val : ℤ) - p.1.val) - n).card =
      ∑ y : ZMod (A0 * M), (univ.filter fun x : ZMod (A0 * M) =>
        (A0 : ℤ) ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.card_filter]
  have hpos : (0 : ℝ) < A0 := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne A0)
  have e : (A0 : ℝ) ^ ((7 : ℝ) / 4) = A0 * (A0 : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [show (7 : ℝ) / 4 = 1 + 3 / 4 by norm_num, Real.rpow_add hpos, Real.rpow_one]
  rw [hsplit, Nat.cast_sum]
  calc ∑ y : ZMod (A0 * M), ((univ.filter fun x : ZMod (A0 * M) =>
        (A0 : ℤ) ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n).card : ℝ)
      ≤ ∑ _y : ZMod (A0 * M), (M : ℝ) * (2 * (A0 : ℝ) ^ ((3 : ℝ) / 4)) :=
        Finset.sum_le_sum fun y _ => card_row_le M n (y.val : ℤ)
    _ = 2 * (M : ℝ) ^ 2 * (A0 : ℝ) ^ ((7 : ℝ) / 4) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, e]
        push_cast; ring

end RamanujanPetersson.EllW2


