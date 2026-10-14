-- Prove2me | solution 1 for Apery.range3_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:47:05.953035+00:00
-- url     : https://prove2.me/submissions/72cf8d43-9007-43eb-b9fc-f351507f47f6

/-
# The inner prime range (source `Apery/Growth/Assembly3.lean`)

Proves the platform theorem `Apery.range3_le` from `Apery.inner_table`,
`Apery.inner_table_k`, `Apery.table_Lp_le`, `Apery.Ctab_le` and the summation lemmas.
Port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceGrowthErrors
import Theorems.Thm_Apery_inner_table
import Theorems.Thm_Apery_inner_table_k
import Theorems.Thm_Apery_table_Lp_le
import Theorems.Thm_Apery_Ctab_le

set_option autoImplicit false

section Port0
/-!
# The inner prime range `K/20 < p ≤ K/3` (source `Apery/Growth/Assembly3.lean`)

This file proves the platform theorem `Apery.range3_le`:

`∑_{K/20 < p ≤ K/3} c(k)(-L_k) ≤ psum fIn 3 20 K + 10^8 θ(40n/3)` for `n ≥ 10400`,

from the per-prime bounds `Apery.table_Lp_le` (via the discrete `Apery.inner_Lp_le`), the
piecewise table equalities `Apery.inner_table`, the k-window `Apery.inner_table_k`, the
additive error `Apery.Ctab_le`, the piece locator and the summation `range_sum_le`.
Faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Finset

namespace Apery

lemma theta_eq_sum_cPrime (t : ℝ) : Chebyshev.theta t = ∑ k ∈ Icc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

lemma sum_cPrime_le_theta (M : ℕ) : ∑ k ∈ Ioc 0 M, cPrime k ≤ Chebyshev.theta M := by
  rw [theta_eq_sum_cPrime, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
  · intro k _ _; unfold cPrime; split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_refl _

lemma cPrime_nonneg' (k : ℕ) : 0 ≤ cPrime k := by
  unfold cPrime; split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl _


lemma floor_Kr_div (n d : ℕ) (hd : 0 < d) : ⌊Kr n / d⌋₊ = 40 * n / d := by
  rw [show Kr n / d = ((40 * n : ℕ) : ℝ) / (d : ℕ) by simp [Kr]]
  exact Nat.floor_div_eq_div _ _


lemma grid_mono {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) :
    t i ≤ t j := by
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · exact (ih (by omega) (by omega)).trans (h j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

lemma pieceIdx_spec {t : ℕ → ℝ} {m : ℕ} (h : ∀ i < m, t i < t (i + 1)) {x : ℝ}
    (h0 : t 0 ≤ x) (hm : x < t m) :
    pieceIdx t m x < m ∧ t (pieceIdx t m x) ≤ x ∧ x < t (pieceIdx t m x + 1) := by
  classical
  unfold pieceIdx
  set i := Nat.findGreatest (fun i => t i ≤ x) m with hi
  have hspec : t i ≤ x := Nat.findGreatest_spec (P := fun i => t i ≤ x) (Nat.zero_le m) h0
  have hle : i ≤ m := Nat.findGreatest_le m
  have hlt : i < m := by
    rcases Nat.lt_or_ge i m with h1 | h1
    · exact h1
    · have : i = m := by omega
      rw [this] at hspec; linarith
  refine ⟨hlt, hspec, ?_⟩
  by_contra hc
  rw [not_lt] at hc
  have := Nat.findGreatest_is_greatest (P := fun i => t i ≤ x) (n := m) (k := i + 1) (by omega)
    (by omega)
  exact this hc


theorem tIn_mono : ∀ i < 125, tIn i < tIn (i + 1) := by
  intro i hi
  interval_cases i <;> simp only [tIn, tInL, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num


lemma tIn_zero : tIn 0 = 3 := by simp [tIn, tInL]
lemma tIn_last : tIn 125 = 20 := by simp [tIn, tInL]

lemma range_sum_le {a b : ℕ} (F : ℕ → ℝ) (f : ℝ → ℝ) (K C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k ∈ Ioc a b, k.Prime → F k ≤ k * f (K / k) + C) :
    ∑ k ∈ Ioc a b, cPrime k * F k ≤
      ∑ k ∈ Ioc a b, (k : ℝ) * cPrime k * f (K / k) + C * Chebyshev.theta b := by
  have hθ : ∑ k ∈ Ioc a b, cPrime k ≤ Chebyshev.theta b := by
    refine le_trans ?_ (sum_cPrime_le_theta b)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Ioc] at hk ⊢; omega
    · intro k _ _; exact cPrime_nonneg' k
  have hterm : ∀ k ∈ Ioc a b, cPrime k * F k ≤ (k : ℝ) * cPrime k * f (K / k) + C * cPrime k := by
    intro k hk
    by_cases hp : k.Prime
    · have := h k hk hp
      have hc := cPrime_nonneg' k
      nlinarith [mul_le_mul_of_nonneg_left this hc]
    · simp [cPrime, hp]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hθ hC]


lemma big_prime_facts {n k : ℕ} (hn : 10400 ≤ n) (hk : n / 10 < k) (hp : k.Prime) :
    7 ≤ k ∧ 2 * (k / 2) + 1 = k ∧ ¬ k * Mcut ≤ 40 * n ∧ 2 * (40 * n) < k ^ 2 ∧
      5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < k ^ 2 ∧ (n : ℝ) ≤ 10 * k := by
  have h10 : n + 1 ≤ 10 * k := by omega
  have hsq : 10400 * n + 700 ≤ k ^ 2 * 100 := by nlinarith
  have hodd' : 2 * (k / 2) + 1 = k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have : 2 ∣ k := ⟨j, by omega⟩
      rcases hp.eq_one_or_self_of_dvd 2 this with h | h
      · omega
      · omega
    · omega
  refine ⟨by omega, hodd', by unfold Mcut; omega, by omega, by omega, ?_⟩
  exact_mod_cast (show n ≤ 10 * k by omega)


lemma range3_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), cPrime k * (-(Lp n k : ℝ)) ≤
      psum fIn 3 20 (Kr n) + 10 ^ 8 * Chebyshev.theta (40 * n / 3 : ℕ) := by
  have hps : psum fIn 3 20 (Kr n) =
      ∑ k ∈ Ioc (2 * n) (40 * n / 3), (k : ℝ) * cPrime k * fIn (Kr n / k) := by
    unfold psum
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num,
      floor_Kr_div n 3 (by norm_num), floor_Kr_div n 20 (by norm_num),
      show 40 * n / 20 = 2 * n by omega]
  rw [hps]
  refine range_sum_le (fun k => -(Lp n k : ℝ)) fIn (Kr n) (10 ^ 8) (by norm_num) fun k hk hp => ?_
  have hk' := Finset.mem_Ioc.mp hk
  obtain ⟨hp7, hodd, hsmall, hsq, hdeg, hn10⟩ := big_prime_facts hn (by omega) hp
  have := Fact.mk hp
  have hin : 3 * k ≤ 40 * n := by have := Nat.div_mul_le_self (40 * n) 3; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hp.pos
  set x : ℝ := 40 * n / k with hx
  have hx3 : 3 ≤ x := by
    rw [hx, le_div_iff₀ hkR]; exact_mod_cast (show 3 * k ≤ 40 * n by omega)
  have hx20 : x < 20 := by
    rw [hx, div_lt_iff₀ hkR]; exact_mod_cast (show 40 * n < 20 * k by omega)
  obtain ⟨hi, hx1, hx2⟩ := pieceIdx_spec tIn_mono (x := x) (by rw [tIn_zero]; exact hx3)
    (by rw [tIn_last]; exact hx20)
  set i := pieceIdx tIn 125 x with hidef
  have hmem : x ∈ Set.Ico (tIn i) (tIn (i + 1)) := ⟨hx1, hx2⟩
  have hkr := inner_table_k i hi x hmem
  have hfl : ⌊x⌋₊ = 40 * n / k := by
    rw [hx, show (40 * n : ℝ) / k = ((40 * n : ℕ) : ℝ) / (k : ℕ) by push_cast; ring,
      Nat.floor_div_eq_div]
  rw [hfl] at hkr
  have hk1 : kloI n k ≤ kIn i := hkr.1
  have hk2 : kIn i ≤ ktopI n k := hkr.2
  have h := table_Lp_le (p := k) (n := n) (by omega) hodd hp7 hsmall hin hsq hdeg (kIn i) hk1 hk2
  have htab := inner_table i hi x hmem
  have hq20 : 40 * n / k ≤ 20 := by
    have : 40 * n < 20 * k := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  have hC := Ctab_le (n := n) (p := k) hq20 hk1 hk2
  unfold fIn
  rw [← hidef, ← htab]
  rw [← hx] at h
  linarith

end Apery

#check @Apery.range3_le
end Port0


open Finset in
/-- The platform target `Apery.range3_le`, restated at top level as `solution`. -/
theorem solution {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      Apery.psum Apery.fIn 3 20 (Apery.Kr n) +
        10 ^ 8 * Chebyshev.theta (40 * n / 3 : ℕ) :=
  Apery.range3_le hn
