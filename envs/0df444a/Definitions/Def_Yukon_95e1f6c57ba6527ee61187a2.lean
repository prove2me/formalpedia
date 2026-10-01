-- Prove2me | Definitions.Def_Yukon_95e1f6c57ba6527ee61187a2
-- name    : Yukon_95e1f6c57ba6527ee61187a2
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:57:02.764567+00:00
-- url     : https://prove2.me/theorems/b9fa1f98-787e-4c57-b5c2-8c90e242a846
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean
--
--   yukon-proof-operation:b65b75f1eeaff629103defbf9964dc0b054ac89c22ca93d5e218d63f5fd62545
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YjY1Yjc1ZjFlZWFmZjYyOTEwM2RlZmJmOTk2NGRjMGIwNTRhYzg5YzIyY2E5M2Q1ZTIxOGQ2M2Y1ZmQ2MjU0NSIsImhhc2giOiJhNjM0ZDQ1YTNhM2I5ODBhOThlZWRmNzI5OThmZjY4N2UzN2YyNjE0ZmQxYmE4NDFjZWY4NjM0NzQ3YmZkYTFiIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85NWUxZjZjNTdiYTY1MjdlZTYxMTg3YTIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e

import Definitions.Def_Yukon_57f2f4a582b59c53cdee835d



import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.CompletePartialOrder
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
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
import Mathlib.Algebra.Order.Floor.Semifield
import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4
import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7
set_option backward.isDefEq.respectTransparency.types false
/-!
# Interleaved Reed-Solomon codes

The `s`-interleaved Reed-Solomon code is the `s`-fold interleave of the Reed-Solomon code of
degree bound `⌊k/s⌋`: each codeword is an `s`-tuple of base codewords, arranged
column-wise, so that the code lives over the alphabet `Fin s → F`.

## Main definitions

* `ReedSolomon.Interleaved.irsCode`

## Main statements

* `ReedSolomon.Interleaved.dim_irsCode_eq_min`, `..._dim_irsCode`, `..._dim_irsCode_of_dvd` —
  the dimension is `s * min ⌊k/s⌋ |L|`, hence `s * ⌊k/s⌋` below saturation and `k` when
  `s ∣ k`.
* `ReedSolomon.Interleaved.minDist_irsCode_eq_minDist_rsCode`,
  `ReedSolomon.Interleaved.minDist_irsCode` — interleaving preserves the minimum block
  distance, which is therefore `|L| - ⌊k/s⌋ + 1`.
* `ReedSolomon.Interleaved.alphabetRate_irsCode_eq_min`,
  `ReedSolomon.Interleaved.alphabetRate_irsCode` — the alphabet-normalized rate is
  `min ⌊k/s⌋ |L| / |L|`, hence `⌊k/s⌋ / |L|` below saturation.
* `ReedSolomon.Interleaved.irs_rate_distance` — the code satisfies the MDS rate-distance
  equation `δ_min = 1 - ρ + 1/n` at that rate, with no divisibility hypothesis.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace ReedSolomon
namespace Interleaved

/-- The `s`-interleaved Reed-Solomon code, the `s`-fold interleave of
`ReedSolomon.code domain (k / s)`, as a `Submodule F (ι → Fin s → F)`.

Note that the inner degree bound is the `Nat` division `⌊k/s⌋`, so the total dimension is
`s * ⌊k/s⌋`, which is `k` only when `s ∣ k`: at `k = 5`, `s = 2` it is `4`. A caller wanting
the `s`-interleave of `ReedSolomon.code domain k'` for a given inner degree bound `k'` should
write `irsCode domain (s * k') s`. -/
noncomputable def irsCode {ι : Type*} {F : Type*} [Semiring F]
    (domain : ι ↪ F) (k s : ℕ) : Submodule F (ι → Fin s → F) :=
  (ReedSolomon.code domain (k / s)) ^⋈ (Fin s)

/-- The dimension of an interleaved Reed-Solomon code is `s * min ⌊k/s⌋ |L|`: interleaving
multiplies the base dimension by `s`, and the base code has dimension `min ⌊k/s⌋ |L|`. -/
lemma dim_irsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) :
    Module.finrank F (irsCode domain k s) = s * min (k / s) (Fintype.card ι) := by
  rw [irsCode, Code.finrank_moduleInterleavedCode, Fintype.card_fin]
  exact congrArg (s * ·) (ReedSolomon.dim_eq_min_deg_card (n := k / s) (α := domain))

/-- Below saturation, `⌊k/s⌋ ≤ |L|`, the dimension is `s * ⌊k/s⌋`. This is `k` only when
`s ∣ k`; see `dim_irsCode_of_dvd`. -/
lemma dim_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = s * (k / s) := by
  rw [dim_irsCode_eq_min domain k s, min_eq_left h_rs_full]

/-- When `s ∣ k` and the base code is below saturation, the dimension is exactly `k`. -/
lemma dim_irsCode_of_dvd {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (hdvd : s ∣ k)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = k := by
  rw [dim_irsCode domain k s h_rs_full, Nat.mul_div_cancel' hdvd]

/-- Interleaving preserves the minimum block distance, so an interleaved Reed-Solomon code
has the minimum distance of its base code.

The metric is the block one on `ι → Fin s → F`: a position counts as a disagreement when the
whole `s`-tuple differs, which is why interleaving leaves it unchanged. Nothing
Reed-Solomon-specific enters; this is `Code.minDist_interleavedCodeSet`. -/
theorem minDist_irsCode_eq_minDist_rsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Code.minDist ((ReedSolomon.code domain (k / s) : Submodule F (ι → F)) : Set (ι → F)) := by
  haveI : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne s))
  rw [irsCode, Code.interleavedCode_eq_interleavedCodeSet_of_moduleCode]
  exact Code.minDist_interleavedCodeSet (κ := Fin s) _

/-- The alphabet-normalized rate of an interleaved Reed-Solomon code is
`min ⌊k/s⌋ |L| / |L|`. The interleaving factor `s` multiplies the dimension and the
alphabet normalization divides it back out, so the rate does not see `s`. -/
lemma alphabetRate_irsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s] :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (min (k / s) (Fintype.card ι) : ℕ) / Fintype.card ι := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  rw [LinearCode.alphabetRate_cast_eq, dim_irsCode_eq_min domain k s, Nat.cast_mul,
    mul_div_mul_left _ _ (ne_of_gt hs)]

/-- Below saturation, `⌊k/s⌋ ≤ |L|`, the alphabet-normalized rate is `⌊k/s⌋ / |L|`. -/
lemma alphabetRate_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s]
    (h_rs_full : k / s ≤ Fintype.card ι) :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (k / s : ℕ) / Fintype.card ι := by
  rw [alphabetRate_irsCode_eq_min domain k s, min_eq_left h_rs_full]

/-- The minimum block distance of an interleaved Reed-Solomon code is `|L| - ⌊k/s⌋ + 1`.

Neither divisibility nor non-saturation is needed: once `⌊k/s⌋ ≥ |L|` the base code is all of
`F^L`, the `Nat` subtraction truncates to `0`, and both sides are `1`.

The hypothesis `0 < ⌊k/s⌋` is necessary: at `k < s` the inner degree bound is `0`, so the
code is `⊥` and its minimum distance is `0`, against a right-hand side of `|L| + 1`. It is
taken explicitly rather than as `[NeZero (k / s)]`, which instance resolution could never
discharge for symbolic `k` and `s`. -/
theorem minDist_irsCode {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] (hks : 0 < k / s) :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Fintype.card ι - k / s + 1 := by
  letI : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
  haveI : NeZero (k / s) := ⟨by omega⟩
  rw [minDist_irsCode_eq_minDist_rsCode, ReedSolomon.minDist_eq_card_sub_min_add_1]
  omega

/-- An interleaved Reed-Solomon code satisfies the MDS rate-distance equation at its
alphabet-normalized rate `ρ`:

  `δ_min (irsCode domain k s) = 1 - ρ + 1/n` .

No divisibility or non-saturation hypothesis is needed, in contrast with
`ReedSolomon.Folded.frs_rate_distance_of_dvd`, because interleaving truncates only once:
the dimension `s * min ⌊k/s⌋ n` and the distance `n - ⌊k/s⌋ + 1` degrade through the same
`min`, and the alphabet normalization cancels the interleaving factor, leaving
`ρ = min ⌊k/s⌋ n / n`. In the saturated regime both sides are `1/n`. -/
theorem irs_rate_distance {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] (hks : 0 < k / s) :
    (Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) : ℝ) / Fintype.card ι
      = 1 - (LinearCode.alphabetRate (irsCode domain k s) : ℝ) + 1 / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmin : min (k / s) (Fintype.card ι) ≤ Fintype.card ι := min_le_right _ _
  rw [minDist_irsCode domain k s hks, alphabetRate_irsCode_eq_min domain k s]
  rw [show Fintype.card ι - k / s + 1 = Fintype.card ι - min (k / s) (Fintype.card ι) + 1 by
        omega,
    Nat.cast_add, Nat.cast_sub hmin, Nat.cast_one]
  field_simp

/-- The `s`-fold interleave of `ReedSolomon.code domain k'` is `irsCode domain (s * k') s`.
Definitional once the degree arithmetic is done. -/
lemma interleavedCodeSet_rsCode_eq_irsCode {ι : Type*} {F : Type*} [Field F]
    (domain : ι ↪ F) (k' s : ℕ) (hs : 0 < s) :
    Code.interleavedCodeSet (κ := Fin s)
        ((ReedSolomon.code domain k' : Submodule F (ι → F)) : Set (ι → F))
      = ((irsCode domain (s * k') s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F)) := by
  rw [irsCode, Nat.mul_div_cancel_left k' hs]
  rfl

end Interleaved
end ReedSolomon


