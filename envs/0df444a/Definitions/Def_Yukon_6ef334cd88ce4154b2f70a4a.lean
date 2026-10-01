-- Prove2me | Definitions.Def_Yukon_6ef334cd88ce4154b2f70a4a
-- name    : Yukon_6ef334cd88ce4154b2f70a4a
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:08:18.078986+00:00
-- url     : https://prove2.me/theorems/3b498c8d-23ec-49b2-aba3-b3846312c3f9
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean
--
--   yukon-proof-operation:64c982efb657494092cafcb73674a3e618710a2c0b30d08e61171f6432a60857
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjRjOTgyZWZiNjU3NDk0MDkyY2FmY2I3MzY3NGEzZTYxODcxMGEyYzBiMzBkMDhlNjExNzFmNjQzMmE2MDg1NyIsImhhc2giOiI2ZTc4ZTk1YTMzNzJkMzljNTkwZWUwMzg1YzZiNjUyN2ZlOTI1ODY3YjYwNzc5OWIxZTVmNjcyMjE3NDYxNzc4Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl82ZWYzMzRjZDg4Y2U0MTU0YjJmNzBhNGEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic

import Definitions.Def_Yukon_940a9691b0192ef0397b04a2

import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4

import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7

import Definitions.Def_Yukon_d283689b285597996aeda737

import Definitions.Def_Yukon_2981f0b15bccec6f5a345fbc

import Definitions.Def_Yukon_8312245af6197ac6ee816a59

import Definitions.Def_Yukon_a1a3aabf93c629033becc7ad



import Mathlib.Data.Matrix.Mul
import Init
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
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
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
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.Defs
import Init.Data.List.FinRange
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Matrix.Reflection
set_option backward.isDefEq.respectTransparency.types false
/-!
  # Berlekamp-Welch decoder algorithm for Reed-Solomon codes.

  Given a codeword `f : F [X], deg f ≤ n`, Berlekamp-Welch decoder
  allows to correct up to `(n - k - 1) / 2` errors and obtain a unique source message.
-/

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}
         {e k : ℕ} {ωs f : Polynomial F}

open Polynomial

section

variable [DecidableEq F]

/-- Berlekamp-Welch decoder for Reed-Solomon codes.

  Given received codeword evaluations with potential errors, attempts to recover the original
  polynomial message or returns `none` if decoding fails.

  ### Parameters:
  - `e : ℕ` - Maximum number of correctable errors
  - `k : ℕ` - Degree bound of message polynomial (`<k`)
  - `[NeZero n]` - Instance that codeword length `n` is non-zero
  - `ωs : Fin n → F` - Evaluation points used during encoding
  - `f : Fin n → F` - Received (possibly corrupted) codeword evaluations

  ### Returns:
  - `some p` if successful (where `p : Polynomial F` is the recovered polynomial)
  - `none` if decoding fails (too many errors or unsolvable system)
-/
noncomputable def decoder (e k : ℕ) [NeZero n] (ωs f : Fin n → F) : Option (Polynomial F) :=
  if ‖f‖₀ ≤ e
  then some 0
  else
    let x := linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    match x with
    | none => none
    | some x =>
      let E := solutionToE e k x
      let Q := solutionToQ e k x
      if Q % E = 0 then
        let p := Q / E
        if Δ₀(f, p.eval ∘ ωs) ≤ e then
          some p
        else
          none
      else
        none

/-- If the Berlekamp-Welch decoder succeeds, the decoded polynomial is within the error bound.

### Parameters:
- `[NeZero n]` - Typeclass ensuring non-zero codeword length
- `ωs : Fin n → F` - Evaluation points used in encoding
- `f : Fin n → F` - Received (possibly corrupted) codeword
- `h` - Hypothesis that decoder succeeded (returns `some p`)
-/
theorem hammingDist_le_of_decoder_eq_some [NeZero n] {ωs f : Fin n → F}
    (h : decoder e k ωs f = some p) : Δ₀(f, p.eval ∘ ωs) ≤ e :=
  by aesop (add simp decoder)

/--
**Correctness theorem for Berlekamp-Welch decoder**:
If a codeword is close to a polynomial `p` of degree `< k`
then the decoder succeeds and returns `some p`.

### Parameters:
- `e k : ℕ` - Error capacity and degree bound
- `[NeZero n]` - Non-zero codeword length
- `ωs : Fin n → F` - Distinct evaluation points (injective mapping)
- `f : Fin n → F` - Received word
- `p : Polynomial F` - Original polynomial message
-/
theorem decoder_eq_some {e k : ℕ} [NeZero n] {ωs f : Fin n → F} {p : Polynomial F}
    (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_deg : p.natDegree < k)
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) : decoder e k ωs f = some p := by
  simp only [decoder]
  split_ifs with hif
  · suffices p = 0 from Option.some_inj.2 this.symm
    refine poly_eq_zero_of_dist_lt h_deg hn h_inj (lt_of_le_of_lt ?p₁ he)
    transitivity ‖f‖₀ + Δ₀(f, p.eval ∘ ωs)
    · convert hammingDist_triangle 0 f (p.eval ∘ ωs) using 1 <;> simp
    · omega
  · rcases hlinsolve : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    · simp only [reduceCtorEq]; exact linsolve_always_some_berlekamp_welch h_deg h_dist hlinsolve
    · by_cases hp : p = 0
      · have : ‖f‖₀ ≤ e := by aesop
        omega
      · have h_cond := linsolve_to_BerlekampWelch_condition hlinsolve
        have h :=
          Q'_div_E'_eq_p
            h_deg he hn h_dist h_inj
            (solutionToQ_ne_zero (not_le.1 hif)
                                (BerlekampWelchCondition_iff_Solution.2 h_cond) h_inj) hp h_cond
        simp_all

/--
**Decoding failure characterization**:
When the decoder returns `none`, no valid polynomial exists within the error bound.

### Theorem Statement:
Given the decoder fails (`decoder e k ωs f = none`),
there cannot exist any polynomial `p` of degree < `k` that is
within `e` Hamming errors of the received word `f`.

### Parameters:
- `e k : ℕ` - Error capacity and degree bound
- `[NeZero n]` - Non-zero codeword length
- `ωs : Fin n → F` - Evaluation points
- `f : Fin n → F` - Received word
-/
theorem not_exists_of_decoder_eq_none {e k : ℕ} [NeZero n] {ωs f : Fin n → F}
    (he : 2 * e < n - k + 1) (hn : k ≤ n)
    (h_inj : Function.Injective ωs)
    (h_none : decoder e k ωs f = none) :
    ¬ ∃ p : F[X], Δ₀(f, p.eval ∘ ωs) ≤ e ∧ p.natDegree < k := by
  rintro ⟨p, hp, hpk⟩
  have := decoder_eq_some he hn h_inj hpk hp
  aesop

end

end BerlekampWelch


