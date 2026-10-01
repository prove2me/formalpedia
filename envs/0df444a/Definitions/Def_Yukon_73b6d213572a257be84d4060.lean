-- Prove2me | Definitions.Def_Yukon_73b6d213572a257be84d4060
-- name    : Yukon_73b6d213572a257be84d4060
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:11:52.084338+00:00
-- url     : https://prove2.me/theorems/f9f0fdc2-fa49-4318-a8fa-fc59bfc8095b
-- title:
--   YukonModule.ArkLib.Data.Matrix.Vandermonde.part0
-- statement:
--   Source module ArkLib.Data.Matrix.Vandermonde.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Matrix/Vandermonde.lean
--
--   yukon-proof-operation:45bdcca4165cc8d44b82d1a460fb8516119fd90b4c287bce4cecc9ba47c25878
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NDViZGNjYTQxNjVjYzhkNDRiODJkMWE0NjBmYjg1MTYxMTlmZDkwYjRjMjg3YmNlNGNlY2M5YmE0N2MyNTg3OCIsImhhc2giOiIzMjg2NGM0N2MzMmMzYjVmNjgwMzM1OTg3YmYyMTgyNTNmOTgxNDIxMmQ1YzNiMjNlYzIzYjRkYTA1NDU4OTQ0Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl83M2I2ZDIxMzU3MmEyNTdiZTg0ZDQwNjAiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7

import Definitions.Def_Yukon_a07d5a446bf8be9c414fdc73

import Definitions.Def_Yukon_ed298d692f02efadb0468be6

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Henselian
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Basic


import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Init
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
set_option backward.isDefEq.respectTransparency.types false
/-!
  # Non-square Vandermonde matrices

  Rectangular Vandermonde matrices `(αᵢ^j)` and their rank, for evaluation maps of univariate
  polynomials over an injective point family. The main results identify the maximal square
  submatrices as ordinary Vandermonde matrices, compute the rank as `min` of the two dimensions
  (`rank_nonsquare_rows_eq_min`), and read `mulVecLin` off the matrix as polynomial evaluation
  (`mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials`). Used by the Reed-Solomon and
  proximity-gap developments.
-/

open Polynomial Matrix Code LinearCode

variable {F ι ι' : Type*}

section

namespace Vandermonde

/-- A non-square Vandermonde matrix. -/
def nonsquare [Semiring F] (ι' : ℕ) (α : ι → F) : Matrix ι (Fin ι') F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F] {ι' : ℕ} {α₁ : ι ↪ F} {α₂ : Fin ι' → F} {i : ι} :
    (nonsquare ι' α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ x.1 := by
  simp [nonsquare, mulVec_eq_sum]

/-- The transpose of a non-square Vandermonde matrix. -/
def nonsquareTranspose [Field F] (ι' : ℕ) (α : ι ↪ F) : Matrix (Fin ι') ι F :=
  (Vandermonde.nonsquare ι' α)ᵀ

section

variable [CommRing F] {m n : ℕ} {α : Fin m → F}

/-- The maximal upper square submatrix of a Vandermonde matrix is a Vandermonde matrix. -/
lemma subUpFull_of_vandermonde_is_vandermonde (h : n ≤ m) :
    Matrix.vandermonde (α ∘ Fin.castLE h) =
  Matrix.subUpFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subUpFull, nonsquare]

/-- The maximal left square submatrix of a Vandermonde matrix is a Vandermonde matrix. -/
lemma subLeftFull_of_vandermonde_is_vandermonde (h : m ≤ n) :
    Matrix.vandermonde α = Matrix.subLeftFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subLeftFull, nonsquare]

section

variable [IsDomain F]

/-- The rank of a non-square Vandermonde matrix with more rows than columns is the number of
  columns. -/
lemma rank_nonsquare_eq_deg_of_deg_le (inj : Function.Injective α) (h : n ≤ m) :
    (Vandermonde.nonsquare (ι' := n) α).rank = n := by
  suffices ((Vandermonde.nonsquare (ι' := n) α).subUpFull (Fin.castLE h)).rank = n by
    exact Matrix.rank_eq_if_subUpFull_eq h this
  rw[
    ←subUpFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_if_det_ne_zero
  ]
  rw [@Matrix.det_vandermonde_ne_zero_iff F _ n _ (α ∘ Fin.castLE h)]
  apply Function.Injective.comp <;> aesop (add simp Fin.castLE_injective)

/-- The rank of a non-square Vandermonde matrix with more columns than rows is the number of rows.
-/
lemma rank_nonsquare_eq_deg_of_ι_le (inj : Function.Injective α) (h : m ≤ n) :
    (Vandermonde.nonsquare (ι' := n) α).rank = m := by
  suffices ((Vandermonde.nonsquare (ι' := n) α).subLeftFull (Fin.castLE h)).rank = m by
    exact Matrix.full_row_rank_via_rank_subLeftFull h this
  rw[
    ←subLeftFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_if_det_ne_zero]
  rw[Matrix.det_vandermonde_ne_zero_iff]
  exact inj

@[simp]
lemma rank_nonsquare_rows_eq_min (inj : Function.Injective α) :
    (Vandermonde.nonsquare (ι' := n) α).rank = min m n := by
  by_cases h : m ≤ n
  · rw [rank_nonsquare_eq_deg_of_ι_le inj h]; simp [h]
  · rw [rank_nonsquare_eq_deg_of_deg_le inj] <;> omega

end

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
    {n : ℕ} [NeZero n] {v : ι ↪ F} {p : F[X]} (h_deg : p.natDegree < n) :
  (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) =
  fun i => p.eval (v i) := by
  ext i
  have hLHS :
      (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) i
        = ∑ x ∈ Finset.range n, (if x < n then p.coeff x * v i ^ x else 0) := by
    simp [nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, Fin.liftF'_p_coeff]
  have hRHS :
      p.eval (v i) = ∑ x ∈ Finset.range n, p.coeff x * v i ^ x :=
    Polynomial.eval_eq_sum_range' (p := p) (x := v i) (n := n) h_deg
  calc
    (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) i
        = ∑ x ∈ Finset.range n, (if x < n then p.coeff x * v i ^ x else 0) := hLHS
    _ = ∑ x ∈ Finset.range n, p.coeff x * v i ^ x := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          simp [Finset.mem_range.mp hx]
    _ = p.eval (v i) := by simp [hRHS]

end

end Vandermonde

end


