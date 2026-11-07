-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
-- name    : QEC_Coding_QuditQubitConversion_FiniteField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:09:38.420823+00:00
-- url     : https://prove2.me/theorems/ae089086-7dae-4b90-9ad2-a531d528a88b
-- title:
--   Finite Field
-- statement:
--   Definitions and structural lemmas for Finite Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/FiniteField.lean

import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
namespace QEC.Coding
noncomputable def f1024Modulus : Polynomial (ZMod 2) :=
  1 + X ^ 3 + X ^ 10
theorem f1024Modulus_natDegree_le : f1024Modulus.natDegree ≤ 10 := by
  have h1 : (1 : Polynomial (ZMod 2)).natDegree ≤ 10 := by simp
  have h3 : (X ^ 3 : Polynomial (ZMod 2)).natDegree ≤ 10 := by simp
  have h10 : (X ^ 10 : Polynomial (ZMod 2)).natDegree ≤ 10 := by simp
  simpa only [f1024Modulus] using
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h3) h10
theorem f1024Modulus_monic : f1024Modulus.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 10 f1024Modulus_natDegree_le
  norm_num [f1024Modulus, coeff_add, coeff_X_pow, coeff_one]
theorem f1024Modulus_natDegree : f1024Modulus.natDegree = 10 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero f1024Modulus_natDegree_le
  norm_num [f1024Modulus, coeff_add, coeff_X_pow, coeff_one]
theorem f1024_dvd_sub_trans {a b c : Polynomial (ZMod 2)}
    (hab : f1024Modulus ∣ a - b) (hbc : f1024Modulus ∣ b - c) :
    f1024Modulus ∣ a - c := by
  rcases hab with ⟨u, hu⟩
  rcases hbc with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = f1024Modulus * u + f1024Modulus * v := by rw [hu, hv]
    _ = f1024Modulus * (u + v) := by ring
theorem f1024_dvd_sq_sub_sq {a b : Polynomial (ZMod 2)}
    (h : f1024Modulus ∣ a - b) : f1024Modulus ∣ a ^ 2 - b ^ 2 := by
  rcases h with ⟨u, hu⟩
  refine ⟨u * (a + b), ?_⟩
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = (f1024Modulus * u) * (a + b) := by rw [hu]
    _ = f1024Modulus * (u * (a + b)) := by ring
noncomputable def f1024R4 : Polynomial (ZMod 2) := X ^ 9 + X ^ 6
noncomputable def f1024R5 : Polynomial (ZMod 2) :=
  X ^ 8 + X ^ 5 + X ^ 4 + X ^ 2 + X
noncomputable def f1024R6 : Polynomial (ZMod 2) :=
  X ^ 9 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + 1
noncomputable def f1024R7 : Polynomial (ZMod 2) := X ^ 9 + X ^ 5 + X ^ 2 + X + 1
noncomputable def f1024R8 : Polynomial (ZMod 2) := X ^ 8 + X ^ 3 + X ^ 2 + X
noncomputable def f1024R9 : Polynomial (ZMod 2) := X ^ 9 + X ^ 4 + X ^ 2
theorem f1024_step3 : f1024Modulus ∣ (X ^ 8 : Polynomial (ZMod 2)) ^ 2 - f1024R4 := by
  refine ⟨X ^ 6, ?_⟩
  simp only [f1024Modulus, f1024R4]
  ring_nf
  reduce_mod_char
theorem f1024_step4 : f1024Modulus ∣ f1024R4 ^ 2 - f1024R5 := by
  refine ⟨X ^ 8 + X ^ 2 + X, ?_⟩
  simp only [f1024Modulus, f1024R4, f1024R5]
  ring_nf
  reduce_mod_char
theorem f1024_step5 : f1024Modulus ∣ f1024R5 ^ 2 - f1024R6 := by
  refine ⟨X ^ 6 + 1, ?_⟩
  simp only [f1024Modulus, f1024R5, f1024R6]
  ring_nf
  reduce_mod_char
theorem f1024_step6 : f1024Modulus ∣ f1024R6 ^ 2 - f1024R7 := by
  refine ⟨X ^ 8 + X ^ 6 + X ^ 2 + X, ?_⟩
  simp only [f1024Modulus, f1024R6, f1024R7]
  ring_nf
  reduce_mod_char
theorem f1024_step7 : f1024Modulus ∣ f1024R7 ^ 2 - f1024R8 := by
  refine ⟨X ^ 8 + X + 1, ?_⟩
  simp only [f1024Modulus, f1024R7, f1024R8]
  ring_nf
  reduce_mod_char
theorem f1024_step8 : f1024Modulus ∣ f1024R8 ^ 2 - f1024R9 := by
  refine ⟨X ^ 6, ?_⟩
  simp only [f1024Modulus, f1024R8, f1024R9]
  ring_nf
  reduce_mod_char
theorem f1024_step9 : f1024Modulus ∣ f1024R9 ^ 2 - X := by
  refine ⟨X ^ 8 + X, ?_⟩
  simp only [f1024Modulus, f1024R9]
  ring_nf
  reduce_mod_char
theorem f1024_frobenius : f1024Modulus ∣ (X ^ 1024 : Polynomial (ZMod 2)) - X := by
  have h0 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 1 - X := by simp
  have h1 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 2 - X ^ 2 := by
    simpa using f1024_dvd_sq_sub_sq h0
  have h2 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 4 - X ^ 4 := by
    simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h1
  have h3 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 8 - X ^ 8 := by
    simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h2
  have h4 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 16 - f1024R4 := by
    apply f1024_dvd_sub_trans (b := (X ^ 8 : Polynomial (ZMod 2)) ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h3
    · exact f1024_step3
  have h5 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 32 - f1024R5 := by
    apply f1024_dvd_sub_trans (b := f1024R4 ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h4
    · exact f1024_step4
  have h6 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 64 - f1024R6 := by
    apply f1024_dvd_sub_trans (b := f1024R5 ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h5
    · exact f1024_step5
  have h7 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 128 - f1024R7 := by
    apply f1024_dvd_sub_trans (b := f1024R6 ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h6
    · exact f1024_step6
  have h8 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 256 - f1024R8 := by
    apply f1024_dvd_sub_trans (b := f1024R7 ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h7
    · exact f1024_step7
  have h9 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 512 - f1024R9 := by
    apply f1024_dvd_sub_trans (b := f1024R8 ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h8
    · exact f1024_step8
  have h10 : f1024Modulus ∣ (X : Polynomial (ZMod 2)) ^ 1024 - X := by
    apply f1024_dvd_sub_trans (b := f1024R9 ^ 2)
    · simpa only [← pow_mul, Nat.reduceMul] using f1024_dvd_sq_sub_sq h9
    · exact f1024_step9
  exact h10
theorem f1024Modulus_ne_one : f1024Modulus ≠ 1 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 10) h
  norm_num [f1024Modulus, coeff_add, coeff_X_pow, coeff_one] at hcoeff
theorem f1024_coprime_degree_two : IsCoprime f1024Modulus (X ^ 4 - X) := by
  refine ⟨X ^ 3 + X ^ 2 + 1, X ^ 9 + X ^ 8 + X ^ 5 + X, ?_⟩
  simp only [f1024Modulus]
  ring_nf
  reduce_mod_char
theorem f1024_coprime_degree_five : IsCoprime f1024Modulus (X ^ 32 - X) := by
  refine ⟨(X ^ 4 + X ^ 2 + 1) +
      (X ^ 22 + X ^ 15 + X ^ 12 + X ^ 8 + X ^ 2 + X) *
        (X ^ 6 + X ^ 4 + X ^ 3 + X + 1),
      X ^ 6 + X ^ 4 + X ^ 3 + X + 1, ?_⟩
  simp only [f1024Modulus]
  ring_nf
  reduce_mod_char
theorem irreducible_dvd_frobenius (g : Polynomial (ZMod 2))
    (hg : g.Monic) (hi : Irreducible g) : g ∣ X ^ (2 ^ g.natDegree) - X := by
  letI : Fact (Irreducible g) := ⟨hi⟩
  let E := AdjoinRoot g
  letI : Module.Finite (ZMod 2) E := hg.finite_adjoinRoot
  letI : Finite E := Module.finite_of_finite (ZMod 2)
  letI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = 2 ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := E), ZMod.card]
    simpa [E] using (AdjoinRoot.powerBasis' hg).finrank
  have hroot : (AdjoinRoot.root g : E) ^ (2 ^ g.natDegree) = AdjoinRoot.root g := by
    rw [← hcard]
    exact FiniteField.pow_card _
  apply AdjoinRoot.mk_eq_zero.mp
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X] using sub_eq_zero.mpr hroot
theorem f1024Modulus_irreducible : Irreducible f1024Modulus := by
  rw [f1024Modulus_monic.irreducible_iff_lt_natDegree_lt f1024Modulus_ne_one]
  intro q hq hqrange hqf
  have hqrange' : q.natDegree ∈ Finset.Ioc 0 5 := by
    simpa [f1024Modulus_natDegree] using hqrange
  have hqpos : 0 < q.natDegree := (Finset.mem_Ioc.mp hqrange').1
  have hqle : q.natDegree ≤ 5 := (Finset.mem_Ioc.mp hqrange').2
  obtain ⟨g, hg, hgi, hgq⟩ :=
    Polynomial.exists_monic_irreducible_factor q (not_isUnit_of_natDegree_pos q hqpos)
  have hgf : g ∣ f1024Modulus := hgq.trans hqf
  have hgle : g.natDegree ≤ 5 :=
    (natDegree_le_of_dvd hgq (ne_zero_of_natDegree_gt hqpos)).trans hqle
  have hgfrob : g ∣ X ^ (Nat.card (ZMod 2)) ^ 10 - X := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hgf.trans f1024_frobenius
  have hgdvdten : g.natDegree ∣ 10 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hgi hgfrob
  have hsmall := irreducible_dvd_frobenius g hg hgi
  interval_cases hdeg : g.natDegree
  · have hpos := hgi.natDegree_pos
    omega
  · have hg2 : g ∣ (X ^ 2 - X : Polynomial (ZMod 2)) := by
      simpa [hdeg] using hsmall
    rcases hg2 with ⟨w, hw⟩
    have hg4 : g ∣ (X ^ 4 - X : Polynomial (ZMod 2)) := by
      refine ⟨w * (X ^ 2 + X + 1), ?_⟩
      calc
        X ^ 4 - X = (X ^ 2 - X) * (X ^ 2 + X + 1) := by ring
        _ = (g * w) * (X ^ 2 + X + 1) := by rw [hw]
        _ = g * (w * (X ^ 2 + X + 1)) := by ring
    exact hgi.not_isUnit (f1024_coprime_degree_two.isUnit_of_dvd' hgf hg4)
  · have hg4 : g ∣ (X ^ 4 - X : Polynomial (ZMod 2)) := by
      simpa [hdeg] using hsmall
    exact hgi.not_isUnit (f1024_coprime_degree_two.isUnit_of_dvd' hgf hg4)
  · norm_num [hdeg] at hgdvdten
  · norm_num [hdeg] at hgdvdten
  · have hg32 : g ∣ (X ^ 32 - X : Polynomial (ZMod 2)) := by
      simpa [hdeg] using hsmall
    exact hgi.not_isUnit (f1024_coprime_degree_five.isUnit_of_dvd' hgf hg32)
noncomputable instance f1024IrreducibleFact : Fact (Irreducible f1024Modulus) :=
  ⟨f1024Modulus_irreducible⟩
noncomputable abbrev F1024 : Type := AdjoinRoot f1024Modulus
noncomputable instance : Module.Finite (ZMod 2) F1024 :=
  f1024Modulus_monic.finite_adjoinRoot
noncomputable instance : Finite F1024 :=
  Module.finite_of_finite (ZMod 2)
noncomputable instance : Fintype F1024 := Fintype.ofFinite F1024
noncomputable def f1024PolynomialBasis : Module.Basis (Fin 10) (ZMod 2) F1024 :=
  (AdjoinRoot.powerBasis' f1024Modulus_monic).basis.reindex
    (finCongr f1024Modulus_natDegree)
noncomputable def f1024Coordinates : F1024 ≃ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  f1024PolynomialBasis.equivFun
noncomputable def f1024Alpha : F1024 := AdjoinRoot.root f1024Modulus
end QEC.Coding


