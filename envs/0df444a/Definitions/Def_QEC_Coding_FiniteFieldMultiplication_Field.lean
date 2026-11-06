-- Prove2me | Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
-- name    : QEC_Coding_FiniteFieldMultiplication_Field
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:14:07.553191+00:00
-- url     : https://prove2.me/theorems/8010c3cd-a229-4f49-8a87-672835948fa6
-- title:
--   Field
-- statement:
--   Definitions and structural lemmas for Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Field.lean

import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
namespace QEC.Coding
noncomputable def f256Modulus : Polynomial (ZMod 2) :=
  X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1
theorem f256Modulus_natDegree_le : f256Modulus.natDegree ≤ 8 := by
  have h8 : (X ^ 8 : Polynomial (ZMod 2)).natDegree ≤ 8 := by simp
  have h5 : (X ^ 5 : Polynomial (ZMod 2)).natDegree ≤ 8 := by simp
  have h4 : (X ^ 4 : Polynomial (ZMod 2)).natDegree ≤ 8 := by simp
  have h3 : (X ^ 3 : Polynomial (ZMod 2)).natDegree ≤ 8 := by simp
  have h1 : (1 : Polynomial (ZMod 2)).natDegree ≤ 8 := by simp
  simpa only [f256Modulus] using
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le h8 h5) h4) h3) h1
theorem f256Modulus_monic : f256Modulus.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 8 f256Modulus_natDegree_le
  norm_num [f256Modulus, coeff_add, coeff_X_pow, coeff_one]
theorem f256Modulus_natDegree : f256Modulus.natDegree = 8 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero f256Modulus_natDegree_le
  norm_num [f256Modulus, coeff_add, coeff_X_pow, coeff_one]
theorem f256Modulus_irreducible : Irreducible f256Modulus := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 17)
    (by norm_num) ?_ ?_
  · refine ⟨X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1, ?_⟩
    rw [cyclotomic_prime (ZMod 2) 17]
    simp only [f256Modulus, Finset.sum_range_succ, Finset.sum_range_zero]
    ring_nf
    reduce_mod_char
  · rw [f256Modulus_natDegree]
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    symm
    apply orderOf_eq_prime_pow (p := 2) (n := 2)
    · intro h
      have hval := congrArg Units.val h
      norm_num [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val] at hval
      exact (by decide +revert : (16 : ZMod 17) ≠ 1) hval
    · apply Units.ext
      norm_num [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
      exact (by decide +revert : (256 : ZMod 17) = 1)
noncomputable instance f256IrreducibleFact : Fact (Irreducible f256Modulus) :=
  ⟨f256Modulus_irreducible⟩
noncomputable abbrev F256 : Type := AdjoinRoot f256Modulus
noncomputable instance : Module.Finite (ZMod 2) F256 :=
  f256Modulus_monic.finite_adjoinRoot
noncomputable instance : Finite F256 :=
  Module.finite_of_finite (ZMod 2)
noncomputable instance : Fintype F256 := Fintype.ofFinite F256
noncomputable def f256PolynomialBasis : Module.Basis (Fin 8) (ZMod 2) F256 :=
  (AdjoinRoot.powerBasis' f256Modulus_monic).basis.reindex
    (finCongr f256Modulus_natDegree)
noncomputable def f256Coordinates : F256 ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  f256PolynomialBasis.equivFun
end QEC.Coding


