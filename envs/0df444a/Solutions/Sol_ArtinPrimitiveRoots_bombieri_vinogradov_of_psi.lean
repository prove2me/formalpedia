-- Prove2me | solution 1 for ArtinPrimitiveRoots.bombieri_vinogradov_of_psi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:47:14.523855+00:00
-- url     : https://prove2.me/submissions/7968753e-93c5-4280-a5c5-b8c2a26e50e0

import Mathlib
import Definitions.Def_ArtinBV
import Definitions.Def_ArtinSieve

section

end

section
/-!
# Discrete partial summation and bounds for character sums
-/

namespace ArtinPrimitiveRoots.BV

open Finset

end ArtinPrimitiveRoots.BV
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinPrimitiveRoots.BV

open Finset

theorem conv_sum {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 (X / a), F a b := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.2.1, p.2.2⟩) (fun p _ => ⟨p.1 * p.2, (p.1, p.2)⟩)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨n, a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨hn0, hnX⟩, hab, -⟩ := h
    subst hab
    have ha : 0 < a := Nat.pos_of_mul_pos_right hn0
    have hb : 0 < b := Nat.pos_of_mul_pos_left hn0
    refine ⟨⟨ha, le_trans (Nat.le_mul_of_pos_right a hb) hnX⟩, hb, ?_⟩
    rw [Nat.le_div_iff_mul_le ha]
    linarith [mul_comm a b]
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Nat.mem_divisorsAntidiagonal] at h ⊢
    obtain ⟨⟨ha, haX⟩, hb, hbX⟩ := h
    rw [Nat.le_div_iff_mul_le ha] at hbX
    refine ⟨⟨Nat.mul_pos ha hb, by linarith [mul_comm a b]⟩, trivial, by positivity⟩
  · rintro ⟨n, a, b⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at h
    obtain ⟨-, hab, -⟩ := h
    subst hab
    rfl
  · rintro ⟨a, b⟩ _
    rfl

/-- The harmonic sum over `(0, X]`. -/
theorem harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

theorem harm_nonneg (X : ℕ) : 0 ≤ ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) :=
  Finset.sum_nonneg fun i _ => by positivity

/-- `n ≤ φ(n) d(n)`. -/
theorem le_totient_mul_card_divisors (n : ℕ) (hn : n ≠ 0) :
    n ≤ n.totient * n.divisors.card := by
  rw [Nat.totient_eq_prod_factorization hn, Nat.card_divisors hn, Finsupp.prod,
    Nat.support_factorization, ← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_le_prod' fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 1 ≤ n.factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hpp hn (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hk]
  have hp2 := hpp.two_le
  simp only [Nat.add_sub_cancel, pow_succ]
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  have : p ≤ (p - 1) * 2 := by omega
  calc p ≤ (p - 1) * 2 := this
    _ ≤ (p - 1) * (k + 1 + 1) := Nat.mul_le_mul_left _ (by omega)

/-- `∑_{m ≤ Q} 1/φ(m) ≤ (1 + log Q)^2`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    ∑ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ)) ≤ (1 + Real.log Q) ^ 2 := by
  have h1 : ∀ m ∈ Ioc 0 Q, (1 / (m.totient : ℝ)) ≤
      ∑ x ∈ m.divisorsAntidiagonal, (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : m ≠ 0 := hm.1.ne'
    have hcard : (m.divisorsAntidiagonal).card = m.divisors.card := by
      rw [← Nat.map_div_right_divisors, Finset.card_map]
    have hval : ∀ x ∈ m.divisorsAntidiagonal, (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) = 1 / m := by
      intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      rw [one_div_mul_one_div, ← Nat.cast_mul, hx.1]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hcard, nsmul_eq_mul]
    have ht : 0 < m.totient := Nat.totient_pos.mpr hm.1
    have key := le_totient_mul_card_divisors m hm0
    have key' : (m : ℝ) ≤ m.totient * m.divisors.card := by exact_mod_cast key
    rw [div_le_iff₀ (by exact_mod_cast ht)]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm.1
    calc (1 : ℝ) = m * (1 / m) := by field_simp
      _ ≤ (m.totient * m.divisors.card) * (1 / m) :=
          mul_le_mul_of_nonneg_right key' (by positivity)
      _ = ↑(m.divisors.card) * (1 / ↑m) * ↑m.totient := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  rw [conv_sum (fun a b => (1 / (a : ℝ)) * (1 / (b : ℝ))) Q]
  calc ∑ a ∈ Ioc 0 Q, ∑ b ∈ Ioc 0 (Q / a), (1 / (a : ℝ)) * (1 / (b : ℝ))
      ≤ ∑ a ∈ Ioc 0 Q, ∑ b ∈ Ioc 0 Q, (1 / (a : ℝ)) * (1 / (b : ℝ)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_right (Nat.div_le_self _ _)) (fun _ _ _ => by positivity)
    _ = (∑ i ∈ Ioc 0 Q, (1 / (i : ℝ))) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (1 + Real.log Q) ^ 2 := pow_le_pow_left₀ (harm_nonneg Q) (harm_le Q) 2

end ArtinPrimitiveRoots.BV
end

section
/-!
# Vaughan's identity and the resulting decomposition of `ψ(X, χ)`
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

end ArtinPrimitiveRoots.BV
end

section
/-!
# Type I bounds in Vaughan's decomposition
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem log_le_of_mem {X n : ℕ} (hn : n ∈ Ioc 0 X) : Real.log n ≤ Real.log X := by
  rw [Finset.mem_Ioc] at hn
  exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)

end ArtinPrimitiveRoots.BV
end

section
/-!
# Comparing `Li` with `∑ 1/log j`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

theorem antitoneOn_inv_log : AntitoneOn (fun t : ℝ => 1 / Real.log t) (Set.Ici 2) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have h1 : 0 < Real.log a := Real.log_pos (by linarith)
  have h2 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  exact one_div_le_one_div_of_le h1 h2

theorem li_sum_compare (k : ℕ) (hk : 2 ≤ k) :
    |ArtinPrimitiveRoots.logIntegral k - ∑ j ∈ Ioc 1 k, 1 / Real.log j| ≤ 1 / Real.log 2 := by
  set f : ℝ → ℝ := fun t => 1 / Real.log t with hf
  set a := k - 2 with ha
  have hk' : (k : ℝ) = 2 + a := by rw [ha]; push_cast [hk]; ring
  have hanti : AntitoneOn f (Set.Icc 2 (2 + a)) :=
    antitoneOn_inv_log.mono (fun t ht => ht.1)
  have hI1 := hanti.integral_le_sum
  have hI2 := hanti.sum_le_integral
  have hli : ArtinPrimitiveRoots.logIntegral k = ∫ x in (2 : ℝ)..2 + a, f x := by
    rw [ArtinPrimitiveRoots.logIntegral, hk']
  have hsum : ∑ j ∈ Ioc 1 k, 1 / Real.log j = ∑ i ∈ range (a + 1), f (2 + i) := by
    rw [show k = 1 + (a + 1) by omega, ← Finset.Ico_add_one_add_one_eq_Ioc,
      Finset.sum_Ico_eq_sum_range]
    rw [show 1 + (a + 1) + 1 - (1 + 1) = a + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]; push_cast; ring_nf
  have hs1 : ∑ i ∈ range (a + 1), f (2 + i) = ∑ i ∈ range a, f (2 + i) + f (2 + a) :=
    Finset.sum_range_succ _ _
  have hs2 : ∑ i ∈ range (a + 1), f (2 + i) = ∑ i ∈ range a, f (2 + (i + 1 : ℕ)) + f 2 := by
    rw [Finset.sum_range_succ']; simp
  have hfa : 0 ≤ f (2 + a) := by
    simp only [hf]; exact one_div_nonneg.mpr (Real.log_nonneg (by have : (0:ℝ) ≤ a := Nat.cast_nonneg a; linarith))
  have hf2 : f 2 = 1 / Real.log 2 := rfl
  rw [hli, hsum, abs_le]
  constructor
  · rw [hs2]; linarith
  · rw [hs1]; linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# From `θ(k; q, a)` to `π(Y; q, a) - Li(Y)/φ(q)` by partial summation
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

/-- Real Abel summation. -/
theorem abel_sum_real (g f : ℕ → ℝ) (s N : ℕ) (hsN : s ≤ N) :
    ∑ k ∈ Ioc s N, g k * f k =
      (∑ j ∈ Ioc s N, g j) * f N - ∑ k ∈ Ico s N, (∑ j ∈ Ioc s k, g j) * (f (k + 1) - f k) := by
  induction N, hsN using Nat.le_induction with
  | base => simp
  | succ N hsN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ico_succ_top hsN]
    ring

/-- `θ(k; q, a)`. -/
noncomputable def thetaq (k q a : ℕ) : ℝ :=
  ∑ j ∈ Ioc 1 k, (if j.Prime ∧ j ≡ a [MOD q] then Real.log j else 0)

/-- The error `G_q(k) = θ(k; q, a) - (k - 1)/φ(q)`. -/
noncomputable def Gq (k q a : ℕ) : ℝ :=
  ∑ j ∈ Ioc 1 k, ((if j.Prime ∧ j ≡ a [MOD q] then Real.log j else 0) - 1 / q.totient)

theorem pi_eq_sum (Y : ℝ) (q a : ℕ) :
    (ArtinPrimitiveRoots.primeCountingAP Y q a : ℝ) =
      ∑ j ∈ Ioc 1 ⌊Y⌋₊, (if j.Prime ∧ j ≡ a [MOD q] then (1 : ℝ) else 0) := by
  rw [ArtinPrimitiveRoots.primeCountingAP, Finset.sum_boole]
  congr 2
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h, hp, hpa⟩; exact ⟨⟨hp.one_lt, by omega⟩, hp, hpa⟩
  · rintro ⟨⟨_, h⟩, hp, hpa⟩; exact ⟨by omega, hp, hpa⟩

theorem li_sub_li_floor (Y : ℝ) (hY : 2 ≤ Y) :
    |ArtinPrimitiveRoots.logIntegral Y - ArtinPrimitiveRoots.logIntegral ⌊Y⌋₊| ≤ 1 / Real.log 2 := by
  set N := ⌊Y⌋₊ with hN
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
    exact_mod_cast this
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYN : Y - N < 1 := by have := Nat.lt_floor_add_one Y; linarith
  have hcont : ∀ a b : ℝ, 2 ≤ a → 2 ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have : 2 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
      (Real.log_pos (by linarith)).ne').continuousWithinAt
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcont 2 N le_rfl hN2)
    (hcont N Y hN2 hY)
  rw [ArtinPrimitiveRoots.logIntegral, ArtinPrimitiveRoots.logIntegral, ← hsplit, add_sub_cancel_left]
  have hb : ∀ t ∈ Set.uIoc (N : ℝ) Y, ‖1 / Real.log t‖ ≤ 1 / Real.log 2 := by
    intro t ht
    rw [Set.uIoc_of_le hNY] at ht
    have h2t : 2 ≤ t := by linarith [ht.1]
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr (Real.log_nonneg (by linarith)))]
    exact one_div_le_one_div_of_le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) h2t)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Y - N)] at this
  have h2 : 0 < 1 / Real.log 2 := by have := Real.log_two_gt_d9; positivity
  nlinarith

/-- The per-modulus partial summation estimate. -/
theorem abs_pi_sub_li_le (Y : ℝ) (hY : 2 ≤ Y) (q a : ℕ) (hq : 1 ≤ q) :
    |(ArtinPrimitiveRoots.primeCountingAP Y q a : ℝ) - ArtinPrimitiveRoots.logIntegral Y / q.totient|
      ≤ |Gq ⌊Y⌋₊ q a| * (1 / Real.log ⌊Y⌋₊) +
        ∑ k ∈ Ico 2 ⌊Y⌋₊, |Gq k q a| * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) + 3 := by
  set N := ⌊Y⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set f : ℕ → ℝ := fun k => 1 / Real.log k with hf
  set g : ℕ → ℝ := fun j => (if j.Prime ∧ j ≡ a [MOD q] then Real.log j else 0) - 1 / q.totient
    with hg
  -- the identity
  have hpi : (ArtinPrimitiveRoots.primeCountingAP Y q a : ℝ) =
      ∑ k ∈ Ioc 1 N, g k * f k + (1 / (q.totient : ℝ)) * ∑ k ∈ Ioc 1 N, f k := by
    rw [pi_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    have hl : Real.log j ≠ 0 := (Real.log_pos (by exact_mod_cast hj.1)).ne'
    simp only [hg, hf]
    split_ifs <;> field_simp <;> ring
  have hG : ∀ k, Gq k q a = ∑ j ∈ Ioc 1 k, g j := fun k => rfl
  have habel := abel_sum_real g f 1 N (by omega)
  -- the `k = 1` term vanishes
  have hIco : ∑ k ∈ Ico 1 N, (∑ j ∈ Ioc 1 k, g j) * (f (k + 1) - f k) =
      ∑ k ∈ Ico 2 N, (∑ j ∈ Ioc 1 k, g j) * (f (k + 1) - f k) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N)]
    simp
  rw [hIco] at habel
  have hfN : 0 ≤ f N := one_div_nonneg.mpr (Real.log_natCast_nonneg N)
  have hmono : ∀ k ∈ Ico 2 N, 0 ≤ f k - f (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    simp only [hf]
    have h1 : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk.1)
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk0 : (0 : ℝ) < k := by linarith
    have h2 : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk0 (by push_cast; linarith)
    have := one_div_le_one_div_of_le h1 h2
    linarith
  have hmain : |∑ k ∈ Ioc 1 N, g k * f k| ≤ |Gq N q a| * f N +
      ∑ k ∈ Ico 2 N, |Gq k q a| * (f k - f (k + 1)) := by
    rw [habel, ← hG]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hfN]
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
      rw [abs_mul, ← hG, abs_sub_comm, abs_of_nonneg (hmono k hk)]
  have hli1 := li_sum_compare N hN2
  have hli2 := li_sub_li_floor Y hY
  rw [← hN] at hli2
  have hl2 : 1 / Real.log 2 < 1.45 := by
    have := Real.log_two_gt_d9
    rw [div_lt_iff₀ (by linarith)]; linarith
  have hφ1 : 1 / (q.totient : ℝ) ≤ 1 := by
    rw [div_le_one hφ]; exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hrest : |(1 / (q.totient : ℝ)) * ∑ k ∈ Ioc 1 N, f k -
      ArtinPrimitiveRoots.logIntegral Y / q.totient| ≤ 3 := by
    have e : (1 / (q.totient : ℝ)) * ∑ k ∈ Ioc 1 N, f k -
        ArtinPrimitiveRoots.logIntegral Y / q.totient =
        (1 / (q.totient : ℝ)) * ((∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N) +
          (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N| ≤ 1 / Real.log 2 := by
      rw [abs_sub_comm]; exact hli1
    have h2 : |ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y| ≤
        1 / Real.log 2 := by rw [abs_sub_comm]; exact hli2
    have h3 := abs_add_le (∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N)
      (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)
    have h4 : 0 ≤ |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N +
        (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)| := abs_nonneg _
    calc 1 / (q.totient : ℝ) * |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N +
          (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)|
        ≤ 1 * |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N +
          (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)| :=
          mul_le_mul_of_nonneg_right hφ1 h4
      _ ≤ 3 := by linarith
  rw [hpi, add_sub_assoc]
  refine (abs_add_le _ _).trans ?_
  have e2 : ∀ k ∈ Ico 2 N, |Gq k q a| * (f k - f (k + 1)) =
      |Gq k q a| * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := fun k _ => rfl
  rw [← Finset.sum_congr rfl e2]
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# Summing the partial-summation estimate over moduli
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

theorem sum_pi_le (Y : ℝ) (hY : 2 ≤ Y) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) (v : ℕ → ℕ)
    (B : ℝ) (hB : ∀ k, 2 ≤ k → k ≤ ⌊Y⌋₊ → ∑ q ∈ T, |Gq k q (v q)| ≤ B) :
    ∑ q ∈ T, |(ArtinPrimitiveRoots.primeCountingAP Y q (v q) : ℝ) -
        ArtinPrimitiveRoots.logIntegral Y / q.totient| ≤ B * (1 / Real.log 2) + 3 * T.card := by
  set N := ⌊Y⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  set f : ℕ → ℝ := fun k => 1 / Real.log k with hf
  have hpt := fun q hq => abs_pi_sub_li_le Y hY q (v q) (hT q hq)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_mul]
  have hmono : ∀ k ∈ Ico 2 N, 0 ≤ 1 / Real.log k - 1 / Real.log (k + 1 : ℕ) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have h1 : 0 < Real.log k := Real.log_pos (by linarith)
    have h2 : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have := one_div_le_one_div_of_le h1 h2
    linarith
  have h1 : (∑ q ∈ T, |Gq N q (v q)|) * (1 / Real.log N) ≤ B * (1 / Real.log N) :=
    mul_le_mul_of_nonneg_right (hB N hN2 le_rfl) (one_div_nonneg.mpr (Real.log_natCast_nonneg N))
  have h2 : ∑ k ∈ Ico 2 N, ∑ q ∈ T, |Gq k q (v q)| * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ))
      ≤ ∑ k ∈ Ico 2 N, B * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.sum_mul]
    have hk := Finset.mem_Ico.mp hk
    exact mul_le_mul_of_nonneg_right (hB k hk.1 hk.2.le) (hmono k (Finset.mem_Ico.mpr hk))
  have htel : ∑ k ∈ Ico 2 N, (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) =
      1 / Real.log 2 - 1 / Real.log N := by
    have := Finset.sum_Ico_sub (fun k : ℕ => -(1 / Real.log k)) (show 2 ≤ N from hN2)
    have e : ∀ k ∈ Ico 2 N, (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) =
        -(1 / Real.log ((k + 1 : ℕ) : ℝ)) - -(1 / Real.log k) := fun k _ => by ring
    rw [Finset.sum_congr rfl e, this]
    push_cast; ring
  rw [← Finset.mul_sum, htel] at h2
  have h3 : ∑ q ∈ T, (3 : ℝ) = 3 * T.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [h3]
  nlinarith

/-- Number of `n ≤ k` in a residue class. -/
theorem card_modEq_le (k q a : ℕ) (_hq : 1 ≤ q) :
    ((Ioc 0 k).filter (fun n => n ≡ a [MOD q])).card ≤ k / q + 1 := by
  have hinj : Set.InjOn (fun n => n / q) ↑((Ioc 0 k).filter (fun n => n ≡ a [MOD q])) := by
    intro n hn n' hn' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hn hn'
    simp only at h
    have e1 : n % q = n' % q := hn.2.trans hn'.2.symm
    rw [← Nat.div_add_mod n q, ← Nat.div_add_mod n' q, h, e1]
  have := Finset.card_le_card_of_injOn (fun n => n / q) (t := range (k / q + 1)) ?_ hinj
  · simpa using this
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioc] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)

theorem psiAP_le (k q a : ℕ) (hq : 1 ≤ q) :
    psiAP k q a ≤ ((k : ℝ) / q + 1) * Real.log k := by
  rw [psiAP]
  calc ∑ n ∈ (Ioc 0 k).filter (fun n => n ≡ a [MOD q]), Λ n
      ≤ ∑ n ∈ (Ioc 0 k).filter (fun n => n ≡ a [MOD q]), Real.log k := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter] at hn
        exact ArithmeticFunction.vonMangoldt_le_log.trans (log_le_of_mem hn.1)
    _ = ((Ioc 0 k).filter (fun n => n ≡ a [MOD q])).card * Real.log k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) / q + 1) * Real.log k := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg k)
        have h1 := card_modEq_le k q a hq
        have h2 : ((k / q : ℕ) : ℝ) ≤ (k : ℝ) / q := Nat.cast_div_le
        have h3 : (((Ioc 0 k).filter (fun n => n ≡ a [MOD q])).card : ℝ) ≤ ((k / q : ℕ) : ℝ) + 1 := by
          exact_mod_cast h1
        linarith

theorem psiAP_nonneg (k q a : ℕ) : 0 ≤ psiAP k q a :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- `|θ(k;q,a) - ψ(k;q,a)| ≤ 2 √k log k`. -/
theorem abs_thetaq_sub_psiAP_le (k q a : ℕ) (hk : 1 ≤ k) :
    |thetaq k q a - psiAP k q a| ≤ 2 * √(k : ℝ) * Real.log k := by
  set F : ℕ → ℝ := fun n => if n.Prime ∧ n ≡ a [MOD q] then Λ n else 0 with hF
  have e1 : thetaq k q a = ∑ n ∈ Ioc 0 k, F n := by
    rw [← Finset.sum_Ioc_consecutive F (Nat.zero_le 1) hk]
    have h0 : ∑ n ∈ Ioc 0 1, F n = 0 := by simp [hF, Nat.not_prime_one]
    rw [h0, zero_add, thetaq]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hF]
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h.1]
    · rfl
  have e2 : psiAP k q a = ∑ n ∈ Ioc 0 k, (if n ≡ a [MOD q] then Λ n else 0) := by
    rw [psiAP, Finset.sum_filter]
  have hdiff : psiAP k q a - thetaq k q a =
      ∑ n ∈ Ioc 0 k, ((if n ≡ a [MOD q] then Λ n else 0) - F n) := by
    rw [e1, e2, Finset.sum_sub_distrib]
  have hlo : 0 ≤ psiAP k q a - thetaq k q a := by
    rw [hdiff]
    refine Finset.sum_nonneg fun n _ => ?_
    simp only [hF]
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]
  have hhi : psiAP k q a - thetaq k q a ≤ ∑ n ∈ (Ioc 0 k).filter (fun n => ¬ n.Prime), Λ n := by
    rw [hdiff, Finset.sum_filter]
    refine Finset.sum_le_sum fun n _ => ?_
    simp only [hF]
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]
  have hcheb := Chebyshev.psi_sub_theta_eq_sum_not_prime (k : ℝ)
  rw [Nat.floor_natCast] at hcheb
  have hle := Chebyshev.psi_sub_theta_le (x := (k : ℝ)) (by exact_mod_cast hk)
  rw [abs_sub_comm, abs_of_nonneg hlo]
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# Elementary asymptotic inequalities
-/

namespace ArtinPrimitiveRoots.BV

open Real

/-- Powers of `2 + log x` are dominated by any power of `x`. -/
theorem polylog_le (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (2 + Real.log x) ^ a ≤ C * x ^ ε := by
  set δ := ε / (a + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(2 + 1 / δ) ^ a, by positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ0.le
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0 hδ0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 2 + Real.log x ≤ (2 + 1 / δ) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  calc (2 + Real.log x) ^ a ≤ ((2 + 1 / δ) * x ^ δ) ^ a :=
        Real.rpow_le_rpow (by positivity) h1 ha
    _ = (2 + 1 / δ) ^ a * x ^ (δ * a) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0]
    _ ≤ (2 + 1 / δ) ^ a * x ^ ε := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity)
        rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem log_two_gt : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem log_pos_of_two_le {x : ℝ} (hx : 2 ≤ x) : 0.69 < Real.log x := by
  have h : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := log_two_gt
  linarith

end ArtinPrimitiveRoots.BV
end

section
/-!
# The per-`k` bound for `∑_q |G_q(k)|`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

theorem Gq_eq (k q a : ℕ) (hk : 1 ≤ k) :
    Gq k q a = thetaq k q a - ((k : ℝ) - 1) / q.totient := by
  rw [Gq, thetaq, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  push_cast [hk]; ring

/-- `|G_q(k)| ≤ |ψ(k;q,a) - k/φ(q)| + 2√k log k + 1`. -/
theorem abs_Gq_le (k q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    |Gq k q a| ≤ |psiAP k q a - k / q.totient| + (2 * √(k : ℝ) * Real.log k + 1) := by
  rw [Gq_eq k q a hk]
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 := abs_thetaq_sub_psiAP_le k q a hk
  have e : thetaq k q a - ((k : ℝ) - 1) / q.totient =
      (thetaq k q a - psiAP k q a) + (psiAP k q a - k / q.totient) + 1 / q.totient := by ring
  rw [e]
  have h2 : |1 / (q.totient : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]; exact hφ
  calc |thetaq k q a - psiAP k q a + (psiAP k q a - k / q.totient) + 1 / q.totient|
      ≤ |thetaq k q a - psiAP k q a| + |psiAP k q a - k / q.totient| + |1 / (q.totient : ℝ)| :=
        abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- Trivial bound for `∑_q |ψ(k;q,a) - k/φ(q)|` over `q ≤ Q`. -/
theorem sum_psiAP_trivial (k Q : ℕ) (T : Finset ℕ) (hT : T ⊆ Icc 1 Q) (v : ℕ → ℕ) :
    ∑ q ∈ T, |psiAP k q (v q) - k / q.totient| ≤
      Real.log k * (k * (1 + Real.log Q) + Q) + k * (1 + Real.log Q) ^ 2 := by
  have hpt : ∀ q ∈ T, |psiAP k q (v q) - k / q.totient| ≤
      Real.log k * (k * (1 / (q : ℝ)) + 1) + k * (1 / (q.totient : ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (hT hq)).1
    have h1 := psiAP_le k q (v q) hq1
    have h0 := psiAP_nonneg k q (v q)
    have h3 : (0 : ℝ) ≤ k / q.totient := by positivity
    rw [abs_le]
    constructor
    · have : (k : ℝ) / q.totient = k * (1 / q.totient) := by ring
      have : 0 ≤ Real.log k * (k * (1 / (q : ℝ)) + 1) := by
        have := Real.log_natCast_nonneg k; positivity
      linarith
    · have e : ((k : ℝ) / q + 1) * Real.log k = Real.log k * (k * (1 / (q : ℝ)) + 1) := by ring
      have : 0 ≤ (k : ℝ) * (1 / (q.totient : ℝ)) := by positivity
      linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hIcc : Icc 1 Q = Ioc 0 Q := by ext q; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc] at hT
  have hS1 : ∑ q ∈ T, (1 / (q : ℝ)) ≤ 1 + Real.log Q :=
    (Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => by positivity)).trans (harm_le Q)
  have hS2 : ∑ q ∈ T, (1 / (q.totient : ℝ)) ≤ (1 + Real.log Q) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => by positivity)).trans
      (sum_inv_totient_le Q)
  have hcard : (T.card : ℝ) ≤ Q := by
    have := Finset.card_le_card hT
    rw [Nat.card_Ioc] at this
    exact_mod_cast (by omega : T.card ≤ Q)
  have hlk := Real.log_natCast_nonneg k
  have hk0 : (0 : ℝ) ≤ k := by positivity
  gcongr

end ArtinPrimitiveRoots.BV
end

section
/-!
# Transfer from `ψ(X; q, a)` to `π(Y; q, a) - Li(Y)/φ(q)`
-/

namespace ArtinPrimitiveRoots.BV

open Finset Real

theorem transfer_E3 {Y ε η : ℝ} (hY : 2 ≤ Y) (hεη : ε ≤ η) (T : Finset ℕ)
    (hcardT : (T.card : ℝ) ≤ Y ^ (1 / 2 - η)) (k : ℕ) (hk : 2 ≤ k) (hkY : (k : ℝ) ≤ Y) :
    (T.card : ℝ) * (2 * √(k : ℝ) * Real.log k + 1) ≤ 3 * (Y ^ (1 - ε) * (2 + Real.log Y) ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hL0 : 0 < Real.log Y := by have := log_pos_of_two_le hY; linarith
  have hℓ1 : 1 ≤ 2 + Real.log Y := by linarith
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hsq : √(k : ℝ) ≤ Y ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow hk0.le hkY (by norm_num)
  have hlk : Real.log k ≤ Real.log Y := Real.log_le_log hk0 hkY
  have hlk0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have e1 : Y ^ (1 / 2 - η) * Y ^ (1 / 2 : ℝ) = Y ^ (1 - η) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  have e2 : Y ^ (1 - η) ≤ Y ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hYe : Y ^ (1 / 2 - η) ≤ Y ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hP : 0 ≤ Y ^ (1 - ε) * (2 + Real.log Y) ^ 2 := by positivity
  have h1 : (T.card : ℝ) * (2 * √(k : ℝ) * Real.log k) ≤
      2 * (Y ^ (1 - ε) * (2 + Real.log Y) ^ 2) := by
    calc (T.card : ℝ) * (2 * √(k : ℝ) * Real.log k)
        ≤ Y ^ (1 / 2 - η) * (2 * Y ^ (1 / 2 : ℝ) * Real.log Y) := by gcongr
      _ = 2 * (Y ^ (1 / 2 - η) * Y ^ (1 / 2 : ℝ)) * Real.log Y := by ring
      _ = 2 * Y ^ (1 - η) * Real.log Y := by rw [e1]
      _ ≤ 2 * Y ^ (1 - ε) * (2 + Real.log Y) ^ 2 := by
          gcongr
          nlinarith
      _ = 2 * (Y ^ (1 - ε) * (2 + Real.log Y) ^ 2) := by ring
  have h2 : (T.card : ℝ) ≤ Y ^ (1 - ε) * (2 + Real.log Y) ^ 2 :=
    (hcardT.trans hYe).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hℓ1))
  nlinarith

theorem transfer_regime_b {Y ε η ρ : ℝ} (hY : 2 ≤ Y) (hη : 0 ≤ η) (hε1 : ε ≤ 1 - ρ) (hεη : ε ≤ η)
    (Q' : ℕ) (hQ'Y : (Q' : ℝ) ≤ Y ^ (1 / 2 - η)) (k : ℕ) (hk : 2 ≤ k) (hkY : (k : ℝ) ≤ Y)
    (hkρ : (k : ℝ) < Y ^ ρ) :
    Real.log k * (k * (1 + Real.log Q') + Q') + k * (1 + Real.log Q') ^ 2 ≤
      3 * (Y ^ (1 - ε) * (2 + Real.log Y) ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hL0 : 0 < Real.log Y := by have := log_pos_of_two_le hY; linarith
  set ℓ := 2 + Real.log Y with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hYe : Y ^ (1 / 2 - η) ≤ Y ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hlogQ : 1 + Real.log Q' ≤ ℓ := by
    have : Real.log Q' ≤ Real.log Y := by
      rcases Nat.eq_zero_or_pos Q' with h0 | h0
      · rw [h0]; simp; linarith
      · exact Real.log_le_log (by exact_mod_cast h0) (hQ'Y.trans
          (Real.rpow_le_self_of_one_le hY1 (by linarith)))
    linarith
  have hlogQ0 : 0 ≤ 1 + Real.log Q' := by have := Real.log_natCast_nonneg Q'; linarith
  have hlk : Real.log k ≤ ℓ := by have := Real.log_le_log hk0 hkY; linarith
  have hlk0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hkε : (k : ℝ) ≤ Y ^ (1 - ε) :=
    hkρ.le.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  have hQε : (Q' : ℝ) ≤ Y ^ (1 - ε) := hQ'Y.trans hYe
  have hYε0 : 0 ≤ Y ^ (1 - ε) := by positivity
  calc Real.log k * (k * (1 + Real.log Q') + Q') + k * (1 + Real.log Q') ^ 2
      ≤ ℓ * (Y ^ (1 - ε) * ℓ + Y ^ (1 - ε)) + Y ^ (1 - ε) * ℓ ^ 2 := by gcongr
    _ = 2 * (Y ^ (1 - ε) * ℓ ^ 2) + ℓ * Y ^ (1 - ε) := by ring
    _ ≤ 3 * (Y ^ (1 - ε) * ℓ ^ 2) := by
        have h1 : ℓ ≤ ℓ ^ 2 := by nlinarith
        have : ℓ * Y ^ (1 - ε) ≤ Y ^ (1 - ε) * ℓ ^ 2 := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left h1 hYε0
        linarith

theorem transfer_poly {Y ε A' C2 : ℝ} (hY : 2 ≤ Y) (hA' : 0 < A')
    (hC2 : (2 + Real.log Y) ^ (A' + 2) ≤ C2 * Y ^ ε) :
    Y ^ (1 - ε) * (2 + Real.log Y) ^ 2 ≤ C2 * (Y * Real.log Y ^ (-A')) := by
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < Real.log Y := by have := log_pos_of_two_le hY; linarith
  set ℓ := 2 + Real.log Y with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have h2 : ℓ ^ (2 : ℕ) * ℓ ^ A' = ℓ ^ (A' + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hℓ0]; congr 1; push_cast; ring
  have h3 : ℓ ^ (-A') ≤ Real.log Y ^ (-A') :=
    Real.rpow_le_rpow_of_nonpos hL0 (by linarith) (by linarith)
  have h4 : ℓ ^ A' * ℓ ^ (-A') = 1 := by rw [← Real.rpow_add hℓ0]; simp
  have h5 : Y ^ (1 - ε) * Y ^ ε = Y := by rw [← Real.rpow_add hY0]; simp
  have hC20 : 0 ≤ C2 := by
    have h6 : 0 < ℓ ^ (A' + 2) := by positivity
    have h7 : 0 < Y ^ ε := by positivity
    by_contra hc; push Not at hc
    have : C2 * Y ^ ε < 0 := mul_neg_of_neg_of_pos hc h7
    linarith
  calc Y ^ (1 - ε) * ℓ ^ 2 = Y ^ (1 - ε) * (ℓ ^ 2 * ℓ ^ A') * ℓ ^ (-A') := by
        rw [mul_assoc (Y ^ (1 - ε)), mul_assoc (ℓ ^ 2), h4, mul_one]
    _ = Y ^ (1 - ε) * ℓ ^ (A' + 2) * ℓ ^ (-A') := by rw [h2]
    _ ≤ Y ^ (1 - ε) * (C2 * Y ^ ε) * ℓ ^ (-A') := by gcongr
    _ = C2 * (Y ^ (1 - ε) * Y ^ ε) * ℓ ^ (-A') := by ring
    _ = C2 * Y * ℓ ^ (-A') := by rw [h5]
    _ ≤ C2 * Y * Real.log Y ^ (-A') := by gcongr
    _ = C2 * (Y * Real.log Y ^ (-A')) := by ring

/-- **Transfer** from `ψ(X; q, a)` to `π(Y; q, a) - Li(Y)/φ(q)` by partial summation. -/
theorem bombieri_vinogradov_of_psi
    (h : ∀ A η : ℝ, 0 < A → 0 < η → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊, |psiAP X q (a q) - X / q.totient|
        ≤ C * (X * log X ^ (-A)))
    (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)),
          |(ArtinPrimitiveRoots.primeCountingAP Y q (v q) : ℝ)
            - ArtinPrimitiveRoots.logIntegral Y / Nat.totient q| ≤
        C * (Y * log Y ^ (-A')) := by
  by_cases hη2 : 1 / 2 ≤ η
  · refine ⟨0, fun Y hY v hv => ?_⟩
    have hempty : (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter
        (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro q - ⟨hq1, hqY⟩
      have : Y ^ (1 / 2 - η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      linarith
    rw [hempty]; simp
  push Not at hη2
  set ρ := (1 - 2 * η) / (1 - η) with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; linarith
  have hρη : ρ * (1 / 2 - η / 2) = 1 / 2 - η := by
    have h1 : (1 - η) ≠ 0 := by linarith
    rw [hρ, div_mul_eq_mul_div, div_eq_iff h1]; ring
  set ε := min (1 - ρ) η with hε
  have hε0 : 0 < ε := lt_min (by linarith) hη
  have hε1 : ε ≤ 1 - ρ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  obtain ⟨C1, hC1⟩ := h A' (η / 2) hA' (by positivity)
  set C1' := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  obtain ⟨C2, hC20, hC2⟩ := polylog_le (A' + 2) ε (by linarith) hε0
  refine ⟨1.45 * (C1' * ρ ^ (-A')) + 12 * C2, fun Y hY v hv => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  set L := Real.log Y with hLdef
  have hL69 : 0.69 < L := log_pos_of_two_le hY
  have hL0 : 0 < L := by linarith
  set ℓ := 2 + L with hℓdef
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hLℓ : L ≤ ℓ := by linarith
  set T := (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter
    (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)) with hT
  set Q' := ⌊Y ^ (1 / 2 - η)⌋₊ with hQ'
  have hTQ : T ⊆ Icc 1 Q' := by
    intro q hq
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hq
    rw [Finset.mem_Icc]
    exact ⟨hq.2.1, Nat.le_floor hq.2.2.le⟩
  have hT1 : ∀ q ∈ T, 1 ≤ q := fun q hq => (Finset.mem_Icc.mp (hTQ hq)).1
  have hYe : Y ^ (1 / 2 - η) ≤ Y ^ (1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hQ'Y : (Q' : ℝ) ≤ Y ^ (1 / 2 - η) := Nat.floor_le (by positivity)
  have hcardT : (T.card : ℝ) ≤ Y ^ (1 / 2 - η) := by
    have := Finset.card_le_card hTQ
    rw [Nat.card_Icc] at this
    have h2 : (T.card : ℝ) ≤ Q' := by exact_mod_cast (by omega : T.card ≤ Q')
    linarith
  have hYeps : 1 ≤ Y ^ (1 - ε) := Real.one_le_rpow hY1 (by linarith)
  set B := C1' * ρ ^ (-A') * Y * L ^ (-A') + 6 * (Y ^ (1 - ε) * ℓ ^ 2) with hB
  have hB0 : 0 ≤ C1' * ρ ^ (-A') * Y * L ^ (-A') := by positivity
  have hP0 : 0 ≤ Y ^ (1 - ε) * ℓ ^ 2 := by positivity
  have hBk : ∀ k, 2 ≤ k → k ≤ ⌊Y⌋₊ → ∑ q ∈ T, |Gq k q (v q)| ≤ B := by
    intro k hk hkN
    have hkY : (k : ℝ) ≤ Y := (Nat.le_floor_iff (by linarith)).mp hkN
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hstep : ∑ q ∈ T, |Gq k q (v q)| ≤
        ∑ q ∈ T, |psiAP k q (v q) - k / q.totient| + T.card * (2 * √(k : ℝ) * Real.log k + 1) := by
      calc ∑ q ∈ T, |Gq k q (v q)| ≤ ∑ q ∈ T, (|psiAP k q (v q) - k / q.totient| +
            (2 * √(k : ℝ) * Real.log k + 1)) :=
            Finset.sum_le_sum fun q hq => abs_Gq_le k q (v q) (by omega) (hT1 q hq)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    refine hstep.trans ?_
    have hE := transfer_E3 hY hεη T hcardT k hk hkY
    by_cases hkρ : Y ^ ρ ≤ k
    · -- regime (a): psi-BV at `k`
      have hTk : T ⊆ Icc 1 ⌊(k : ℝ) ^ (1 / 2 - η / 2)⌋₊ := by
        intro q hq
        simp only [hT, Finset.mem_filter, Finset.mem_range] at hq
        rw [Finset.mem_Icc]
        refine ⟨hq.2.1, Nat.le_floor ?_⟩
        have e : Y ^ (1 / 2 - η) = (Y ^ ρ) ^ (1 / 2 - η / 2) := by
          rw [← Real.rpow_mul hY0.le, hρη]
        have : (Y ^ ρ) ^ (1 / 2 - η / 2) ≤ (k : ℝ) ^ (1 / 2 - η / 2) :=
          Real.rpow_le_rpow (by positivity) hkρ (by linarith)
        linarith [hq.2.2]
      have hsum := (Finset.sum_le_sum_of_subset_of_nonneg hTk (fun _ _ _ => abs_nonneg _)).trans
        (hC1 k hk v hv)
      have hlogk : ρ * L ≤ Real.log k := by
        have := Real.log_le_log (by positivity) hkρ
        rwa [Real.log_rpow hY0] at this
      have hpow : Real.log k ^ (-A') ≤ ρ ^ (-A') * L ^ (-A') := by
        rw [← Real.mul_rpow hρ0.le hL0.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hlogk (by linarith)
      have hmain : C1 * (k * Real.log k ^ (-A')) ≤ C1' * ρ ^ (-A') * Y * L ^ (-A') := by
        calc C1 * (k * Real.log k ^ (-A')) ≤ C1' * (k * Real.log k ^ (-A')) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ C1' * (Y * (ρ ^ (-A') * L ^ (-A'))) := by gcongr
          _ = C1' * ρ ^ (-A') * Y * L ^ (-A') := by ring
      rw [hB]
      linarith
    · -- regime (b): trivial bound
      push Not at hkρ
      have htriv := sum_psiAP_trivial k Q' T hTQ v
      have hb := transfer_regime_b hY hη.le hε1 hεη Q' hQ'Y k hk hkY hkρ
      rw [hB]
      linarith
  have hfinal := sum_pi_le Y hY T hT1 v B hBk
  refine hfinal.trans ?_
  have hl2 : 1 / Real.log 2 ≤ 1.45 := by
    have := Real.log_two_gt_d9
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]; linarith
  have hcard' : 3 * (T.card : ℝ) ≤ 3 * (Y ^ (1 - ε) * ℓ ^ 2) := by
    have h1 := hcardT.trans hYe
    have h2 : Y ^ (1 - ε) ≤ Y ^ (1 - ε) * ℓ ^ 2 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ (n := 2) hℓ1)
    linarith
  have hpoly : Y ^ (1 - ε) * ℓ ^ 2 ≤ C2 * (Y * L ^ (-A')) := transfer_poly hY hA' (hC2 Y hY1)
  have hB0' : 0 ≤ B := by rw [hB]; positivity
  have hB' : B * (1 / Real.log 2) ≤ 1.45 * B := by nlinarith
  have hYL : 0 ≤ Y * L ^ (-A') := by positivity
  calc B * (1 / Real.log 2) + 3 * (T.card : ℝ) ≤ 1.45 * B + 3 * (Y ^ (1 - ε) * ℓ ^ 2) := by
        linarith
    _ = 1.45 * (C1' * ρ ^ (-A')) * (Y * L ^ (-A')) + 11.7 * (Y ^ (1 - ε) * ℓ ^ 2) := by
        rw [hB]; ring
    _ ≤ 1.45 * (C1' * ρ ^ (-A')) * (Y * L ^ (-A')) + 11.7 * (C2 * (Y * L ^ (-A'))) := by
        gcongr
    _ ≤ (1.45 * (C1' * ρ ^ (-A')) + 12 * C2) * (Y * L ^ (-A')) := by
        have : 0 ≤ C2 * (Y * L ^ (-A')) := by positivity
        nlinarith

end ArtinPrimitiveRoots.BV
end

open ArtinPrimitiveRoots Finset Real in
theorem solution
    (h : ∀ A η : ℝ, 0 < A → 0 < η → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊, |psiAP X q (a q) - X / q.totient|
        ≤ C * (X * log X ^ (-A)))
    (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)),
          |(primeCountingAP Y q (v q) : ℝ) - logIntegral Y / Nat.totient q| ≤
        C * (Y * log Y ^ (-A')) :=
  ArtinPrimitiveRoots.BV.bombieri_vinogradov_of_psi h A' η hA' hη
