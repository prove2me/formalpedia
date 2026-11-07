-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
-- name    : QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:39:16.643933+00:00
-- url     : https://prove2.me/theorems/36eb0547-a982-4010-99ec-05686786dfcc
-- title:
--   Compatible Prime Degree
-- statement:
--   Definitions and structural lemmas for Compatible Prime Degree, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
structure CompatibleDegreePrime (A : Nat) where
  p : Nat
  prime : p.Prime
  oneModFour : p % 4 = 1
  blockDvdDegree : A ∣ p + 1
def CompatibleDegreePrime.blocks {A : Nat} (a : CompatibleDegreePrime A) : Nat :=
  (a.p + 1) / A
theorem two_mul_sub_one_coprime_four_mul
    (A : Nat) (hA : 0 < A) (hOdd : Odd A) :
    (2 * A - 1).Coprime (4 * A) := by
  have hCoprimeA : (2 * A - 1).Coprime A := by
    have hRewrite : 2 * A - 1 = (A - 1) + A := by omega
    rw [hRewrite, Nat.coprime_add_self_left]
    exact (Nat.coprime_self_sub_left (by omega : 1 ≤ A)).2 (by simp)
  have hCoprimeFour : (2 * A - 1).Coprime 4 := by
    obtain ⟨k, rfl⟩ := hOdd
    have hRewrite : 2 * (2 * k + 1) - 1 = 4 * k + 1 := by omega
    rw [hRewrite]
    simp
  exact Nat.Coprime.mul_right hCoprimeFour hCoprimeA
theorem exists_compatibleDegreePrime_gt
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    ∃ a : CompatibleDegreePrime A, B < a.p := by
  have hCoprime := two_mul_sub_one_coprime_four_mul A hA hOdd
  obtain ⟨p, hpB, hpPrime, hpMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B
      (q := 4 * A) (a := 2 * A - 1) (by positivity) hCoprime
  have hResidueLt : 2 * A - 1 < 4 * A := by omega
  have hpMod' : p % (4 * A) = 2 * A - 1 := by
    change p % (4 * A) = (2 * A - 1) % (4 * A) at hpMod
    rw [Nat.mod_eq_of_lt hResidueLt] at hpMod
    exact hpMod
  have hpModA : p % A = A - 1 := by
    calc
      p % A = (p % (4 * A)) % A := by
        symm
        exact Nat.mod_mod_of_dvd p (by exact ⟨4, by ring⟩)
      _ = (2 * A - 1) % A := by rw [hpMod']
      _ = A - 1 := by
        have hRewrite : 2 * A - 1 = A + (A - 1) := by omega
        rw [hRewrite, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hpModFour : p % 4 = 1 := by
    calc
      p % 4 = (p % (4 * A)) % 4 := by
        symm
        exact Nat.mod_mod_of_dvd p (by exact ⟨A, by ring⟩)
      _ = (2 * A - 1) % 4 := by rw [hpMod']
      _ = 1 := by
        obtain ⟨k, rfl⟩ := hOdd
        omega
  have hDegree : A ∣ p + 1 := by
    by_cases hAOne : A = 1
    · subst A
      simp
    · rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpModA]
      have hOneMod : 1 % A = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hOneMod, Nat.sub_add_cancel (by omega : 1 ≤ A), Nat.mod_self]
  exact ⟨⟨p, hpPrime, hpModFour, hDegree⟩, hpB⟩
noncomputable def compatibleDegreePrimeAt
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    CompatibleDegreePrime A :=
  Classical.choose (exists_compatibleDegreePrime_gt A B hA hOdd)
end QEC.Coding.TannerLiftedProduct


