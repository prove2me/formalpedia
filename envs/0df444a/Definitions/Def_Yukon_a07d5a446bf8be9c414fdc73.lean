-- Prove2me | Definitions.Def_Yukon_a07d5a446bf8be9c414fdc73
-- name    : Yukon_a07d5a446bf8be9c414fdc73
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:51:56.449032+00:00
-- url     : https://prove2.me/theorems/19c48875-1646-441c-98e5-e1ecd6f677a1
-- title:
--   YukonModule.ArkLib.Data.Polynomial.Interface.part0
-- statement:
--   Source module ArkLib.Data.Polynomial.Interface. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Polynomial/Interface.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Polynomial/Interface.lean
--
--   yukon-proof-operation:64a8fcf1131b65dcaecb8c0e341c863fce03f2cc348b27f9a37f7be4cec2599c
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjRhOGZjZjExMzFiNjVkY2FlY2I4YzBlMzQxYzg2M2ZjZTAzZjJjYzM0OGIyN2Y5YTM3ZjdiZTRjZWMyNTk5YyIsImhhc2giOiJjZTQ4NTA5Y2YyODM1OGE0YTIyYjkzNjdiNGU3ZDAyNmZkYTI4MWRjMDM3YTIzYzcwNGI1ZDc3YTlhMWRiOTdhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9hMDdkNWE0NDZiZjhiZTljNDE0ZmRjNzMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Definitions.Def_Yukon_27544cfc264ef7c169a23dd9

import Mathlib.RingTheory.Polynomial.Basic

import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Init
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
set_option backward.isDefEq.respectTransparency.types false
/-! # Polynomial Coefficient Interfaces -/


section PolynomialInterface

open Polynomial

variable {F : Type*} [Semiring F] {deg : ℕ} {coeffs : Fin deg → F}

lemma natDegree_lt_of_lbounded_zero_coeff {p : F[X]} [NeZero deg]
    (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  by_contra hn
  have hge : deg ≤ p.natDegree := Nat.le_of_not_gt hn
  have hp : p ≠ 0 := by
    intro heq
    have hz : deg = 0 := by simpa [heq] using hge
    exact (NeZero.ne deg) hz
  apply (Polynomial.leadingCoeff_ne_zero.mpr hp)
  simpa only [Polynomial.coeff_natDegree] using h p.natDegree hge

def coeffsOfPolynomial (p : F[X]) : Fin deg → F :=
  fun ⟨x, _⟩ ↦ p.coeff x

variable [DecidableEq F]

def polynomialOfCoeffs (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi ⟨a, w⟩))
  ⟩

@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg
    [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg :
    (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])

@[simp]
lemma polynomialOfCoeffs_mem_degreeLT [NeZero deg] :
    polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs :
    Fin.liftF' (polynomialOfCoeffs coeffs).coeff = coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

lemma coeff_polynomialOfCoeffs_eq_coeffs' :
    (polynomialOfCoeffs coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffs)

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs'' :
    (polynomialOfCoeffs coeffs).coeff = Fin.liftF coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

@[simp]
lemma polynomialOfCoeffs_eq_zero :
    polynomialOfCoeffs coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  constructor <;> intro h
  · intro x hx
    have : (polynomialOfCoeffs coeffs).coeff x = (0 : F[X]).coeff x := by rw [h]
    simp only [polynomialOfCoeffs, ne_eq, coeff_ofFinsupp, Finsupp.coe_mk, coeff_zero,
      dite_eq_right_iff] at this
    exact this hx
  · ext m
    rw [coeff_polynomialOfCoeffs_eq_coeffs']
    simp [h]

lemma polynomialOfCoeffs_coeffsOfPolynomial {p : F[X]}
    (h : p.natDegree + 1 = deg) : polynomialOfCoeffs (coeffsOfPolynomial (deg := deg) p) = p := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))

@[simp]
lemma coeffsOfPolynomial_polynomialOfCoeffs :
    coeffsOfPolynomial (polynomialOfCoeffs coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfCoeffs : (polynomialOfCoeffs coeffs).support =
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

@[simp]
lemma eval_polynomialsOfCoeffs [NeZero deg] {α : F} :
    (polynomialOfCoeffs coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  simp [eval_eq_sum, sum_def, Fin.liftF]

@[simp]
lemma isRoot_polynomialsOfCoeffs {x : F} :
    IsRoot (polynomialOfCoeffs coeffs) x ↔ eval x (polynomialOfCoeffs coeffs) = 0 := by rfl

end PolynomialInterface


