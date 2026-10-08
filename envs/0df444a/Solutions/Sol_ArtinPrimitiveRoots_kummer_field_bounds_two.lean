-- Prove2me | solution 1 for ArtinPrimitiveRoots.kummer_field_bounds_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T09:13:32.062071+00:00
-- url     : https://prove2.me/submissions/81831fcc-8ff5-4007-9320-656ef73ec802
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Theorems.Thm_ArtinPrimitiveRoots_kummer_field_degree_discr
import Theorems.Thm_ArtinPrimitiveRoots_kummer_zero_free_of_hecke
import Theorems.Thm_ArtinPrimitiveRoots_hecke_zero_free

namespace ArtinPrimitiveRoots.Lemma91two

open NumberField Polynomial

theorem disc_le_pow (a : ℤ) (ha : 1 ≤ |a|) (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (|a| : ℝ) ^ (q - 1)) ^ (q - 1) ≤
      ((q : ℝ) ^ 2 * (|a| : ℝ)) ^ (q * (q - 1)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ha1 : (1 : ℝ) ≤ (|a| : ℝ) := by exact_mod_cast ha
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_pow, ← pow_mul]
  have e1 : q * (q - 2) ≤ q * (q - 1) := Nat.mul_le_mul_left _ (by omega)
  have e2 : (q - 1) * (q - 1) ≤ q * (q - 1) := Nat.mul_le_mul_right _ (by omega)
  have h1 : (q : ℝ) ^ (q * (q - 2)) ≤ (q : ℝ) ^ (q * (q - 1)) := pow_le_pow_right₀ hq1 e1
  have h2 : (|a| : ℝ) ^ ((q - 1) * (q - 1)) ≤ (|a| : ℝ) ^ (q * (q - 1)) :=
    pow_le_pow_right₀ ha1 e2
  have p1 : (0 : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) := by positivity
  have p2 : (0 : ℝ) ≤ (q : ℝ) ^ (q * (q - 1)) := by positivity
  have p3 : (0 : ℝ) ≤ (|a| : ℝ) ^ ((q - 1) * (q - 1)) := by positivity
  rw [show (2 * (q * (q - 1))) = q * (q - 1) + q * (q - 1) by ring, pow_add]
  calc (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ (q * (q - 1)) * (|a| : ℝ) ^ ((q - 1) * (q - 1)))
      ≤ (q : ℝ) ^ (q * (q - 1)) * ((q : ℝ) ^ (q * (q - 1)) * (|a| : ℝ) ^ (q * (q - 1))) := by
        gcongr
    _ = _ := by ring

theorem log_bound (a : ℤ) (ha : 1 ≤ |a|) (q : ℕ) (hq : 3 ≤ q) (D : ℤ) (hD : D ≠ 0)
    (hle : (|D| : ℝ) ≤
      (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (|a| : ℝ) ^ (q - 1)) ^ (q - 1)) :
    Real.log |(D : ℝ)| + ((q * (q - 1) : ℕ) : ℝ) ≤
      (3 + Real.log (|a| : ℝ)) * ((q * (q - 1) : ℕ) : ℝ) * Real.log (2 * q) := by
  have hq1 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have ha1 : (1 : ℝ) ≤ (|a| : ℝ) := by exact_mod_cast ha
  have h := hle.trans (disc_le_pow a ha q (by omega))
  set n : ℕ := q * (q - 1)
  have hDpos : (0 : ℝ) < |(D : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hD
  have hlog : Real.log |(D : ℝ)| ≤ n * Real.log ((q : ℝ) ^ 2 * (|a| : ℝ)) := by
    rw [← Real.log_pow]
    apply Real.log_le_log hDpos
    simpa [Int.cast_abs] using h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hL1 : 1 ≤ Real.log (2 * q) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hLq : Real.log q ≤ Real.log (2 * q) := Real.log_le_log (by positivity) (by linarith)
  have hla : 0 ≤ Real.log (|a| : ℝ) := Real.log_nonneg ha1
  have hn : (0 : ℝ) ≤ n := by positivity
  have k1 := mul_nonneg hn (sub_nonneg.2 hLq)
  have k2 := mul_nonneg hn (sub_nonneg.2 hL1)
  have k3 := mul_nonneg (mul_nonneg hn hla) (sub_nonneg.2 hL1)
  push_cast at hlog ⊢
  nlinarith

theorem zero_free (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime)
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    DedekindZeroFreeRight K (1 - 1 / 10 ^ 6) := by
  have : NeZero (12 * q) := ⟨by have := hq.pos; omega⟩
  have : NeZero (((12 * q : ℕ)) : ℚ) := ⟨by have := hq.pos; positivity⟩
  have : IsCyclotomicExtension {12 * q} ℚ (CyclotomicField (12 * q) ℚ) :=
    CyclotomicField.isCyclotomicExtension _ _
  exact kummer_zero_free_of_hecke a ha q hq _ (by norm_num) (CyclotomicField (12 * q) ℚ)
    (fun 𝔪 h𝔪 χ => hecke_zero_free (12 * q) (by have := hq.pos; omega) (dvd_mul_right 12 q)
      (CyclotomicField (12 * q) ℚ) 𝔪 h𝔪 χ) K

theorem main (a : ℤ) (ha : 1 < |a|) (ℓ q : ℕ) (hℓ : ℓ.Prime) (hℓa : (ℓ : ℤ) ∣ a)
    (hq : q.Prime) (hq3 : 3 ≤ q) (hqℓ : q ≠ ℓ) (hqv : padicValInt ℓ a < q)
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    Module.finrank ℚ K = q * (q - 1) ∧
    (|discr K| : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (|a| : ℝ) ^ (q - 1)) ^ (q - 1) ∧
    Real.log |(discr K : ℝ)| + Module.finrank ℚ K ≤
      (3 + Real.log (|a| : ℝ)) * Module.finrank ℚ K * Real.log (2 * q) ∧
    (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * q →
      ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P →
        P.ramificationIdx ℤ = 1) ∧
    DedekindZeroFreeRight K (1 - 1 / 10 ^ 6) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨h1, h2, h3⟩ := kummer_field_degree_discr a ℓ q hℓ hℓa ha0 hq hqℓ hqv K
  refine ⟨h1, h2, ?_, h3, zero_free a ha0 q hq K⟩
  rw [h1]
  exact log_bound a ha.le q hq3 (discr K) (discr_ne_zero K) h2

end ArtinPrimitiveRoots.Lemma91two

open NumberField Polynomial ArtinPrimitiveRoots in
theorem solution :
    ∃ B : ℝ, ∀ q : ℕ, q.Prime → 5 ≤ q →
      ∀ (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (2 : ℚ))],
        Module.finrank ℚ K = q * (q - 1) ∧
        (|discr K| : ℝ) ≤ (q : ℝ) ^ (q * (q - 2)) * ((q : ℝ) ^ q * (2 : ℝ) ^ (q - 1)) ^ (q - 1) ∧
        Real.log |(discr K : ℝ)| + Module.finrank ℚ K ≤
          B * Module.finrank ℚ K * Real.log (2 * q) ∧
        (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ 2 * q →
          ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P →
            P.ramificationIdx ℤ = 1) ∧
        DedekindZeroFreeRight K (1 - 1 / 10 ^ 6) := by
  refine ⟨3 + Real.log (|((2 : ℤ) : ℝ)|), fun q hq hq5 K _ _ hK => ?_⟩
  have : IsSplittingField ℚ K (X ^ q - C (((2 : ℤ)) : ℚ)) := by
    rw [Int.cast_ofNat]; exact hK
  have hv : padicValInt 2 (2 : ℤ) = 1 := by
    simp [padicValInt]
  have := Lemma91two.main (2 : ℤ) (by norm_num) 2 q Nat.prime_two dvd_rfl hq (by omega)
    (by omega) (by omega) K
  simpa using this

