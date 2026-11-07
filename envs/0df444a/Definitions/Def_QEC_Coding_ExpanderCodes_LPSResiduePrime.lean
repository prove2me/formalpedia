-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
-- name    : QEC_Coding_ExpanderCodes_LPSResiduePrime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:30:05.765242+00:00
-- url     : https://prove2.me/theorems/13270a37-1168-40f8-873b-59ef56524c21
-- title:
--   LPSResidue Prime
-- statement:
--   Definitions and structural lemmas for LPSResidue Prime, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
def specialLinearTwoEquivDetKer (q : ℕ) [Fact q.Prime] :
    SL(2, ZMod q) ≃
      (Matrix.GeneralLinearGroup.det :
        GL (Fin 2) (ZMod q) →* (ZMod q)ˣ).ker where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by simp⟩
  invFun A := ⟨(A.1 : Matrix (Fin 2) (Fin 2) (ZMod q)), by
    have h := congrArg Units.val A.property
    exact h⟩
  left_inv A := by rfl
  right_inv A := by
    ext
    rfl
structure LPSResiduePrime (p : ℕ) where
  degreePrime : p.Prime
  degreeModFour : p % 4 = 1
  q : ℕ
  prime : q.Prime
  large : 4 * p < q
  modFour : q % 4 = 1
  residue : @legendreSym q ⟨prime⟩ p = 1
instance (a : LPSResiduePrime p) : Fact a.q.Prime := ⟨a.prime⟩
def lpsPrimeCandidate (p B q : ℕ) : Prop :=
  max B (4 * p) < q ∧ q.Prime ∧ q % (4 * p) = 1
instance (p B : ℕ) : DecidablePred (lpsPrimeCandidate p B) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
theorem exists_lpsPrimeCandidate {p : ℕ} (hp : p.Prime) (B : ℕ) :
    ∃ q, lpsPrimeCandidate p B q := by
  obtain ⟨q, hBound, hPrime, hMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (4 * p))
      (q := 4 * p) (a := 1)
      (mul_ne_zero (by norm_num) hp.ne_zero) (by simp)
  refine ⟨q, hBound, hPrime, ?_⟩
  have hFour : 1 < 4 * p := by have := hp.two_le; omega
  exact Nat.mod_eq_of_modEq hMod hFour
def lpsLeastPrimeAbove {p : ℕ} (hp : p.Prime) (B : ℕ) : ℕ :=
  Nat.find (exists_lpsPrimeCandidate hp B)
theorem lpsLeastPrimeAbove_spec {p : ℕ} (hp : p.Prime) (B : ℕ) :
    lpsPrimeCandidate p B (lpsLeastPrimeAbove hp B) :=
  Nat.find_spec (exists_lpsPrimeCandidate hp B)
def lpsResiduePrimeAt {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) : LPSResiduePrime p := by
  let q := lpsLeastPrimeAbove hp B
  have hSpec := lpsLeastPrimeAbove_spec hp B
  have hBound := hSpec.1
  have hPrime := hSpec.2.1
  have hMod := hSpec.2.2
  have hModEq : Nat.ModEq (4 * p) q 1 := by
    exact hMod.trans (Nat.mod_eq_of_lt (by have := hp.two_le; omega)).symm
  have hModFour : q % 4 = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hModEq)
    norm_num
  have hModP : q % p = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hModEq)
    exact hp.one_lt
  let : Fact q.Prime := ⟨hPrime⟩
  let : Fact p.Prime := ⟨hp⟩
  have hNeTwo : q ≠ 2 := by omega
  have hResidue : @legendreSym q ⟨hPrime⟩ p = 1 := by
    change legendreSym q (p : ℤ) = 1
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp4 hNeTwo,
      legendreSym.mod]
    have hModInt : (q : ℤ) % p = 1 := by exact_mod_cast hModP
    rw [hModInt]
    simp
  exact ⟨hp, hp4, q, hPrime,
    lt_of_le_of_lt (Nat.le_max_right B (4 * p)) hBound,
    hModFour, hResidue⟩
end QEC.Coding.TannerLiftedProduct


