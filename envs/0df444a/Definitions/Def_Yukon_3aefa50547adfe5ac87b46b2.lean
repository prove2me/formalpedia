-- Prove2me | Definitions.Def_Yukon_3aefa50547adfe5ac87b46b2
-- name    : Yukon_3aefa50547adfe5ac87b46b2
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:56:46.274255+00:00
-- url     : https://prove2.me/theorems/544ec2a9-6a32-4496-be00-9f8df6611276
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ErrorBound.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ErrorBound.lean
--
--   yukon-proof-operation:324b9f1e42af161cf4297cef903290e4551b5fad69b776960c8427d88b9cd60f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjM1ZGQ4N2ZiMTIwNGZjMDVhODMzODE5ZjFkMWIzY2NhMDQ1YzlhYzQ2MWZmZDUxMTFmNTZhNmRjZGRjMzc0ZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjMyNGI5ZjFlNDJhZjE2MWNmNDI5N2NlZjkwMzI5MGU0NTUxYjVmYWQ2OWI3NzY5NjBjODQyN2Q4OGI5Y2Q2MGYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zYWVmYTUwNTQ3YWRmZTVhYzg3YjQ2YjIiLCJ2IjoyfQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/


import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e



import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.Lagrange
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
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
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
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.List.FinRange
import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Definitions.Def_Yukon_6ef334cd88ce4154b2f70a4a
import Definitions.Def_Yukon_57f2f4a582b59c53cdee835d
import Definitions.Def_Yukon_242be9c48cf0d0c464d1328d
import Definitions.Def_Yukon_1841f2bfe33370de8d932885
import Definitions.Def_Yukon_7cd44868014c2b6d6c065fa9
import Definitions.Def_Yukon_766b34592bec7fcb9f69f5d5
import Definitions.Def_Yukon_73cb364285b0db29404203c2
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityGap

open NNReal Finset Function Code
open scoped BigOperators LinearCode

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ (0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ ((1-ρ)/2 , 1 - √ρ)`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := LinearCode.rate (ReedSolomon.code domain deg)
  if δ ∈ Set.Icc 0 ((1 - ρ) / 2) then
    Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ) / 2) (1 - ρ.sqrt) then
    letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
    ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
  else
    0

omit [DecidableEq ι] in
theorem errorBound_eq_n_div_q_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    errorBound δ deg domain = Fintype.card ι / Fintype.card F := by
  classical
  let C : LinearCode ι F := ReedSolomon.code domain deg
  let n : ℕ := Fintype.card ι
  let kdim : ℕ := Module.finrank F C
  let d : ℕ := Code.dist (C : Set (ι → F))
  have hk : kdim ≤ n := by
    have hk' : Module.finrank F C ≤ Module.finrank F (ι → F) :=
      Submodule.finrank_le (R := F) (M := (ι → F)) C
    simpa [n, kdim, Module.finrank_pi] using hk'
  have hSB : kdim ≤ n - d + 1 := by
    simpa [n, d, kdim] using (LinearCode.singleton_bound_linear (LC := C))
  have hdle : d ≤ n := by
    exact Code.dist_le_card (C := (C : Set (ι → F)))
  have hdistNat : d - 1 ≤ n - kdim := by
    omega
  -- Compare the unique-decoding radius with the rate-based threshold.
  have hrel :
      relativeUniqueDecodingRadius (ι := ι) (F := F) (C := C) ≤
        ((1 - (↑(LinearCode.rate C) : ℝ≥0)) / 2) := by
    have hUDR :
        relativeUniqueDecodingRadius (ι := ι) (F := F) (C := C) =
          (((d : ℝ≥0) - 1) / 2) / (n : ℝ≥0) := by
      simp [Code.relativeUniqueDecodingRadius, d, n]
    have hrate : (↑(LinearCode.rate C) : ℝ≥0) = (kdim : ℝ≥0) / (n : ℝ≥0) := by
      simp [LinearCode.rate, LinearCode.dim, LinearCode.length, kdim, n]
    -- Cast the distance-gap inequality into `ℝ≥0`.
    have hdistNN : ((d : ℝ≥0) - 1) ≤ (n - kdim : ℝ≥0) := by
      exact_mod_cast hdistNat
    -- The blocklength is positive because the index type is nonempty.
    have hn0 : (n : ℝ≥0) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      exact Fintype.card_ne_zero (α := ι)
    -- Rewrite the rate term using the codimension expression.
    have hR :
        ((1 : ℝ≥0) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2 =
          ((n - kdim : ℝ≥0) / 2) / (n : ℝ≥0) := by
      calc
        ((1 : ℝ≥0) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2
            = (((n : ℝ≥0) / (n : ℝ≥0)) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2 := by
                rw [← div_self hn0]
        _ = (((n : ℝ≥0) - (kdim : ℝ≥0)) / (n : ℝ≥0)) / 2 := by
              rw [← NNReal.sub_div (a := (n : ℝ≥0)) (b := (kdim : ℝ≥0)) (c := (n : ℝ≥0))]
        _ = ((n - kdim : ℝ≥0) / (n : ℝ≥0)) / 2 := by
              simp
        _ = ((n - kdim : ℝ≥0) / 2) / (n : ℝ≥0) := by
              simp [div_div, mul_comm]
    -- Substitute the distance and rate identities into the target bound.
    rw [hUDR, hrate, hR]
    gcongr
  -- The assumed radius bound puts `δ` in the unique-decoding branch.
  have hmem : δ ∈ Set.Icc 0 ((1 - (↑(LinearCode.rate C) : ℝ≥0)) / 2) := by
    refine ⟨by simp, le_trans hδ hrel⟩
  -- Evaluate `errorBound` on that branch.
  simp [errorBound, C, hmem]

end CoreResults

end ProximityGap


