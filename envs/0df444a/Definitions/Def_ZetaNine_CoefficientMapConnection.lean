-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapConnection
-- name    : ZetaNine_CoefficientMapConnection
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-04T11:09:22.133532+00:00
-- url     : https://prove2.me/theorems/365148c0-a3da-4c9e-be31-9f99ca5605ac
-- title:
--   The original polynomial D/H connection and genuine Fin15 coordinate map
-- statement:
--   Define the original rational polynomial coordinates u=t(t+n), v=t(t+n-1) for n>=1, D=(u-n-1)^10, the true H difference polynomial, actual Fin15 coordinate map, and original three-factor Z targets. The linear-map proof fields contain complete local linearity proofs. No kernel or bijectivity property is supplied as a premise.
-- source:
--   Actual original D/H connection system; frozen source SHA256 098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8.

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Polynomial

namespace ZetaNine.CoefficientMapConnection

def connectionU (n : ℕ) : ℚ[X] := X * (X + C (n : ℚ))

def connectionV (n : ℕ) : ℚ[X] := X * (X + C ((n - 1 : ℕ) : ℚ))

def connectionD (n : ℕ) : ℚ[X] := (connectionU n - C ((n : ℚ) + 1)) ^ 10

def connectionH (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10 * q.comp (connectionV n) -
    (X + C (2 * (n : ℚ) + 1)) * (X - 1) ^ 10 *
      q.comp ((X + 1) * (X + C (n : ℚ)))

def connectionReflection (n : ℕ) : ℚ[X] := -X - C (n : ℚ)

def coefficientPolynomial (d : ℕ) (c : Fin d → ℚ) : ℚ[X] :=
  ∑ i : Fin d, c i • (X ^ i.val)

def inputP (c : Fin 15 → ℚ) : ℚ[X] :=
  coefficientPolynomial 5 (fun i => c ⟨i.val, by omega⟩)

def inputQ (c : Fin 15 → ℚ) : ℚ[X] :=
  coefficientPolynomial 10 (fun i => c ⟨i.val + 5, by omega⟩)

def connectionOperator (n : ℕ) (P q : ℚ[X]) : ℚ[X] :=
  connectionD n * P.comp (connectionU n) + connectionH n q

def connectionLinearMap (n : ℕ) : (Fin 15 → ℚ) →ₗ[ℚ] (Fin 15 → ℚ) where
  toFun c i := (connectionOperator n (inputP c) (inputQ c)).coeff (2 * i.val)
  map_add' c d := by
    classical
    funext i
    have hP : inputP (c + d) = inputP c + inputP d :=
      ((by
    have coefficientPolynomial_add (d : ℕ) (c e : Fin d → ℚ) :
        coefficientPolynomial d (c + e) = coefficientPolynomial d c + coefficientPolynomial d e := by
      classical
      simp only [coefficientPolynomial, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    exact coefficientPolynomial_add) :
    (∀ (d : ℕ) (c e : Fin d → ℚ),
      ZetaNine.CoefficientMapConnection.coefficientPolynomial d (c + e) =
        ZetaNine.CoefficientMapConnection.coefficientPolynomial d c +
          ZetaNine.CoefficientMapConnection.coefficientPolynomial d e)) 5 _ _
    have hQ : inputQ (c + d) = inputQ c + inputQ d :=
      ((by
    have coefficientPolynomial_add (d : ℕ) (c e : Fin d → ℚ) :
        coefficientPolynomial d (c + e) = coefficientPolynomial d c + coefficientPolynomial d e := by
      classical
      simp only [coefficientPolynomial, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    exact coefficientPolynomial_add) :
    (∀ (d : ℕ) (c e : Fin d → ℚ),
      ZetaNine.CoefficientMapConnection.coefficientPolynomial d (c + e) =
        ZetaNine.CoefficientMapConnection.coefficientPolynomial d c +
          ZetaNine.CoefficientMapConnection.coefficientPolynomial d e)) 10 _ _
    simp only [hP, hQ, ((by
    have connectionOperator_add (n : ℕ) (P Q q r : ℚ[X]) :
        connectionOperator n (P + Q) (q + r) =
          connectionOperator n P q + connectionOperator n Q r := by
      simp only [connectionOperator, connectionH, add_comp, mul_add]
      ring
    exact connectionOperator_add) :
    (∀ (n : ℕ) (P Q q r : ℚ[X]),
      ZetaNine.CoefficientMapConnection.connectionOperator n (P + Q) (q + r) =
        ZetaNine.CoefficientMapConnection.connectionOperator n P q +
          ZetaNine.CoefficientMapConnection.connectionOperator n Q r)), coeff_add, Pi.add_apply]
  map_smul' a c := by
    classical
    funext i
    have hP : inputP (a • c) = a • inputP c := ((by
    have coefficientPolynomial_smul (d : ℕ) (a : ℚ) (c : Fin d → ℚ) :
        coefficientPolynomial d (a • c) = a • coefficientPolynomial d c := by
      classical
      simp only [coefficientPolynomial, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    exact coefficientPolynomial_smul) :
    (∀ (d : ℕ) (a : ℚ) (c : Fin d → ℚ),
      ZetaNine.CoefficientMapConnection.coefficientPolynomial d (a • c) =
        a • ZetaNine.CoefficientMapConnection.coefficientPolynomial d c)) 5 a _
    have hQ : inputQ (a • c) = a • inputQ c := ((by
    have coefficientPolynomial_smul (d : ℕ) (a : ℚ) (c : Fin d → ℚ) :
        coefficientPolynomial d (a • c) = a • coefficientPolynomial d c := by
      classical
      simp only [coefficientPolynomial, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    exact coefficientPolynomial_smul) :
    (∀ (d : ℕ) (a : ℚ) (c : Fin d → ℚ),
      ZetaNine.CoefficientMapConnection.coefficientPolynomial d (a • c) =
        a • ZetaNine.CoefficientMapConnection.coefficientPolynomial d c)) 10 a _
    simp only [hP, hQ, ((by
    have connectionOperator_smul (n : ℕ) (a : ℚ) (P q : ℚ[X]) :
        connectionOperator n (a • P) (a • q) = a • connectionOperator n P q := by
      simp only [connectionOperator, connectionH, smul_comp, mul_smul_comm, smul_sub, smul_add]
    exact connectionOperator_smul) :
    (∀ (n : ℕ) (a : ℚ) (P q : ℚ[X]),
      ZetaNine.CoefficientMapConnection.connectionOperator n (a • P) (a • q) =
        a • ZetaNine.CoefficientMapConnection.connectionOperator n P q)), coeff_smul, Pi.smul_apply, RingHom.id_apply]

def connectionZ (n : ℕ) : ℚ[X] :=
  (X - C (((n : ℚ) + 1) * (2 * (n : ℚ) + 1))) *
    (X - C (((n : ℚ) + 2) * (2 * (n : ℚ) + 2))) *
    (X - C (((n : ℚ) + 3) * (2 * (n : ℚ) + 3)))

def connectionTarget (n r : ℕ) : ℚ[X] :=
  C ((((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 7) * connectionZ n *
    (X - C ((n : ℚ) + 1)) ^ r

end ZetaNine.CoefficientMapConnection


