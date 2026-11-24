-- Prove2me | Definitions.Def_CSL_Shared_Programs_RationalScalar
-- name    : CSL_Shared_Programs_RationalScalar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:12:05.501351+00:00
-- url     : https://prove2.me/theorems/53122077-9ac3-4bcf-a3ea-0e9198ec5dcc
-- title:
--   Coded sorting library: Shared / Programs / RationalScalar
-- statement:
--   Module `CodedSorting.Shared.Programs.RationalScalar` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A rational diagonal uses its fixed integer numerator and denominator,
--   not a coefficient of size depending on the modulus. All statements use the
--   already-chosen specialization, and hence never choose a different prime.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.RationalScalar

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_MatrixFactorization
import Mathlib.RingTheory.Int.Basic

/-! A rational diagonal uses its fixed integer numerator and denominator,
not a coefficient of size depending on the modulus. All statements use the
already-chosen specialization, and hence never choose a different prime. -/

namespace CSL.RationalScalar

open MatrixFactorization

variable {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
variable {A : K → Matrix I I ℚ} (F : SpecializedFamily A)

theorem coefficient_denominator_identity (k : K) (i j : I) :
    ((A k i j).den : CoeffRing F.denominator) * F.coefficients k i j =
      ((A k i j).num : CoeffRing F.denominator) := by
  apply intoRat_injective F.denominator F.denominator_ne_zero
  rw [map_mul, F.coefficient_spec, map_natCast, map_intCast]
  rw [mul_comm]
  exact (eq_div_iff (by exact_mod_cast (A k i j).den_nz)).mp
    (Rat.num_div_den (A k i j)).symm

/-- Bézout's identity for the reduced numerator and denominator ensures that
the denominator is a unit in the actual localization supplied by F. -/
theorem denominator_isUnit (k : K) (i j : I) :
    IsUnit ((A k i j).den : CoeffRing F.denominator) := by
  have hcop : IsCoprime (A k i j).num ((A k i j).den : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using (A k i j).reduced)
  have hc := hcop.map (Int.castRingHom (CoeffRing F.denominator))
  apply hc.isUnit_of_dvd'
  · exact ⟨F.coefficients k i j, (coefficient_denominator_identity F k i j).symm⟩
  · exact dvd_rfl

theorem reduced_denominator_isUnit (k : K) (i j : I) (f : ℕ) :
    IsUnit ((A k i j).den : ZMod (F.prime ^ f)) := by
  simpa using (denominator_isUnit F k i j).map (F.reduce f)

theorem reduced_denominator_identity (k : K) (i j : I) (f : ℕ) :
    ((A k i j).den : ZMod (F.prime ^ f)) * F.matrix f k i j =
      ((A k i j).num : ZMod (F.prime ^ f)) := by
  first
  | exact congrArg (F.reduce f) (coefficient_denominator_identity F k i j)
  | (have h_sx := congrArg (F.reduce f) (coefficient_denominator_identity F k i j); simp only [map_mul, map_natCast, map_intCast] at h_sx ⊢; exact h_sx)
  | (have h_sx := congrArg (F.reduce f) (coefficient_denominator_identity F k i j); simp only [map_mul, map_natCast, map_intCast] at h_sx; exact h_sx)
  | (simp only [map_mul, map_natCast, map_intCast]; exact congrArg (F.reduce f) (coefficient_denominator_identity F k i j))

theorem denominator_coprime (k : K) (i j : I) (f : ℕ) :
    (A k i j).den.Coprime (F.prime ^ f) :=
  (ZMod.isUnit_iff_coprime _ _).mp (reduced_denominator_isUnit F k i j f)

theorem numerator_isUnit (k : K) (i j : I) (h : A k i j ≠ 0) (f : ℕ) :
    IsUnit ((A k i j).num : ZMod (F.prime ^ f)) := by
  rw [← reduced_denominator_identity F k i j f]
  exact (reduced_denominator_isUnit F k i j f).mul
    (F.preserves_nonzero_entry_unit k i j h f)

theorem numerator_coprime (k : K) (i j : I) (h : A k i j ≠ 0) (f : ℕ) :
    (A k i j).num.natAbs.Coprime (F.prime ^ f) := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  have hu := numerator_isUnit F k i j h f
  cases hn : (A k i j).num with
  | ofNat n => simpa [hn] using hu
  | negSucc n =>
    simpa [hn] using hu.neg

/-- Multiplication by the specialized rational is exactly fixed signed integer
multiplication followed by multiplication by the denominator unit's inverse. -/
theorem scalar_factorization (k : K) (i j : I) (f : ℕ) :
    F.matrix f k i j = ((A k i j).num : ZMod (F.prime ^ f)) *
      (↑(reduced_denominator_isUnit F k i j f).unit⁻¹ : ZMod (F.prime ^ f)) := by
  let u := (reduced_denominator_isUnit F k i j f).unit
  have hu : (u : ZMod (F.prime ^ f)) = (A k i j).den := IsUnit.unit_spec _
  calc
    F.matrix f k i j = (F.matrix f k i j) * ((u : ZMod (F.prime ^ f)) * ↑u⁻¹) := by
      rw [Units.mul_inv, mul_one]
    _ = (((A k i j).den : ZMod (F.prime ^ f)) * F.matrix f k i j) * ↑u⁻¹ := by
      rw [hu]; ring
    _ = _ := by rw [reduced_denominator_identity F k i j f]

end CSL.RationalScalar


