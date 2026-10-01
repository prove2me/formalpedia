-- Prove2me | Definitions.Def_Yukon_940a9691b0192ef0397b04a2
-- name    : Yukon_940a9691b0192ef0397b04a2
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:59:07.736115+00:00
-- url     : https://prove2.me/theorems/5d5ab16e-b222-48de-8b99-38c4029fe52d
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.Basic.DecodingRadius.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.Basic.DecodingRadius.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/Basic/DecodingRadius.lean
--
--   yukon-proof-operation:72f67956ba4fb7c5fcb78d66bd325e1b52a452e78108cc40c6de8544a9bf49fa
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NzJmNjc5NTZiYTRmYjdjNWZjYjc4ZDY2YmQzMjVlMWI1MmE0NTJlNzgxMDhjYzQwYzZkZTg1NDRhOWJmNDlmYSIsImhhc2giOiJhOTgxMTNmYmFiZDU1NWYzYTg3YTZjOThhZDlmZTY4YTdhNzdjYTg5NGNkZTNiNTc3ZDJmODM0YTdjOTM1MjY3Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85NDBhOTY5MWIwMTkyZWYwMzk3YjA0YTIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import Definitions.Def_Yukon_d283689b285597996aeda737



import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
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
import Init
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
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
set_option backward.isDefEq.respectTransparency.types false
/-!
# Decoding Radius for Codes

This module contains absolute and relative unique decoding radius definitions and the
standard lemmas relating decoding-radius bounds to code distance.
-/

namespace Code

noncomputable section

open NNReal
open scoped NNReal
section DecodingRadius

/-- The unique decoding radius: `≤ ⌊(d-1)/2⌋` for any code `C`. -/
noncomputable def uniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) : ℕ := (‖C‖₀ - 1) / 2 -- Nat.division instead of Nat.floor

alias UDR := uniqueDecodingRadius

/-- The relative unique decoding radius, obtained from the absolute radius by normalizing with the
block length. This also works with `≤`. -/
noncomputable def relativeUniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) : NNReal :=
  (((‖C‖₀ : NNReal) - 1) / 2) / (Fintype.card ι : NNReal)
-- TODO: define `Johnson bound` radius, capacity bounds, etc for generic code `C`

alias relUDR := relativeUniqueDecodingRadius

@[simp]
lemma uniqueDecodingRadius_eq_floor_div_2 {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) :
  Code.uniqueDecodingRadius C = Nat.floor (((‖C‖₀ - 1) : NNReal) / 2) := by
  rw [uniqueDecodingRadius]
  apply Eq.symm
  -- ⊢ ↑((‖C‖₀ - 1) / 2) ≤ (↑‖C‖₀ - 1) / 2 ∧ (↑‖C‖₀ - 1) / 2 < ↑((‖C‖₀ - 1) / 2) + 1
  set d := ‖C‖₀
  -- 4. Set up aliases for the real-valued numbers
  set x_nat : NNReal := ((d - 1 : ℕ) : NNReal)
  set x_nnreal : NNReal := (((d : NNReal) - 1) : NNReal)
  -- 5. These two real numbers are actually equal
  have h_eq : x_nat = x_nnreal := by
    -- rw [NNReal.sub_eq_cast_sub, NNReal.coe_nat_cast]
    dsimp only [x_nat, x_nnreal]
    by_cases h_d_ge_1 : d ≥ 1
    · simp only [Nat.cast_tsub, Nat.cast_one]
    · have h_d_eq_0 : d = 0 := by omega
      rw [h_d_eq_0]
      simp only [zero_tsub, CharP.cast_eq_zero]
  rw [←h_eq]; dsimp [x_nat];
  let res := Nat.floor_div_eq_div  (K := NNReal) (m := (‖C‖₀ - 1)) (n := 2)
  rw [Nat.cast_ofNat] at res
  exact res

/-- Given an error/proximity parameter `e` within the unique decoding radius of a code `C` where
`‖C‖₀ > 0`, this lemma proves the standard bound `2 * e < d`
(i.e. condition of `Code.eq_of_lt_dist`). -/
lemma UDRClose_iff_two_mul_proximity_lt_d_UDR {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) [NeZero (‖C‖₀)]
    {e : ℕ} : e ≤ Code.uniqueDecodingRadius (C := C) ↔ 2 * e < ‖C‖₀ :=
  (Nat.two_mul_lt_iff_le_half_of_sub_one (a := e) (b := ‖C‖₀)
    (h_b_pos := by exact Nat.pos_of_neZero ‖C‖₀)).symm

/-- A stronger version of `distFromCode_eq_of_lt_half_dist`:
If two codewords `v` and `w` are both within the `uniqueDecodingRadius` of
`u` (i.e. `2 * Δ₀(u, v) < ‖C‖₀ and 2 * Δ₀(u, w) < ‖C‖₀`), then they must be equal. -/
theorem eq_of_le_uniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) (u : ι → F) {v w : ι → F}
    (hv : v ∈ C) (hw : w ∈ C)
    (huv : Δ₀(u, v) ≤ Code.uniqueDecodingRadius C)
    (huw : Δ₀(u, w) ≤ Code.uniqueDecodingRadius C) : v = w := by
  -- Handle the edge case where distance is 0 (trivial code)
  by_cases hd : ‖C‖₀ = 0
  · simp only [uniqueDecodingRadius] at huv huw
    simp only [hd, zero_tsub, Nat.zero_div, nonpos_iff_eq_zero, hammingDist_eq_zero] at huv huw
    rw [←huv, ←huw]
  · -- Main Case: d > 0
    apply eq_of_lt_dist hv hw
    calc
      Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
      _ = Δ₀(u, v) + Δ₀(u, w)        := by simp only [hammingDist_comm]
      _ ≤ Code.uniqueDecodingRadius C + Code.uniqueDecodingRadius C := by gcongr
      _ < ‖C‖₀                          := by
        -- Proof that 2 * ⌊(d-1)/2⌋ < d
        simp only [uniqueDecodingRadius]
        -- 2 * ((d - 1) / 2) ≤ d - 1
        have h_div : 2 * ((‖C‖₀ - 1) / 2) ≤ ‖C‖₀ - 1 := by
          rw [mul_comm]
          apply Nat.div_mul_le_self (m := ‖C‖₀ - 1) (n := 2)
        -- Since d ≠ 0, d - 1 < d
        have h_sub : ‖C‖₀ - 1 < ‖C‖₀ := Nat.pred_lt hd
        omega

/--
A word `u` is within the `uniqueDecodingRadius` of a code `C` if and only if
there exists *exactly one* codeword `v` in `C` that is that close.
-/
theorem UDR_close_iff_exists_unique_close_codeword {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    Δ₀(u, C) ≤ Code.uniqueDecodingRadius C ↔ ∃! v ∈ C, Δ₀(u, v) ≤ Code.uniqueDecodingRadius C := by
  -- 1. Define t (radius) and d (distance) for brevity
  set t := Code.uniqueDecodingRadius C
  set d := ‖C‖₀
  constructor
  · -- (→) Direction 1: "Close" implies "Uniquely Close"
    intro h_dist_le_t
    -- 2. First, prove *existence*
    let v := pickClosestCodeword_of_Nonempty_Code (C := C) (u := u)
    have h_close_to_v : Δ₀(u, v) ≤ t := by
      rw [distFromPickClosestCodeword_of_Nonempty_Code (C := C) (u := u)] at h_dist_le_t
      simp only [Nat.cast_le] at h_dist_le_t
      exact h_dist_le_t
    have h_exists : ∃ v, v ∈ C ∧ Δ₀(u, v) ≤ t := by
      use v
      simp only [Subtype.coe_prop, true_and]
      exact h_close_to_v
    -- 3. Second, prove *uniqueness*
    have h_uniq : ∀ (v₁ : ι → F) (v₂ : ι → F),
      v₁ ∈ C → v₂ ∈ C → Δ₀(u, v₁) ≤ t → Δ₀(u, v₂) ≤ t → v₁ = v₂ := by
      intro v₁ v₂ hv₁_mem hv₂_mem h_dist_v₁ h_dist_v₂
      -- We will use the triangle inequality to bound the distance between v₁ and v₂
      have h_dist_v1_v2 : Δ₀(v₁, v₂) ≤ Δ₀(v₁, u) + Δ₀(u, v₂) := by
        exact hammingDist_triangle v₁ u v₂
      -- The distance is symmetric
      rw [hammingDist_comm v₁ u] at h_dist_v1_v2
      -- Substitute the known bounds `≤ t`
      have h_le_2t : Δ₀(v₁, v₂) ≤ t + t :=
        h_dist_v1_v2.trans (Nat.add_le_add h_dist_v₁ h_dist_v₂)
      rw [←Nat.two_mul] at h_le_2t
      -- 4. Now, we show that `2 * t < d`
      -- We handle the main case (d ≥ 2) and the trivial case (d < 2) separately
      by_cases h_d_ge_2 : d ≥ 2
      · -- Case 1: d ≥ 2 (the standard case)
        -- We have t = ⌊(d-1)/2⌋. We know 2 * ⌊(d-1)/2⌋ ≤ d-1
        have h_2t_le_d_minus_1 : 2 * t ≤ d - 1 := by
          dsimp only [d, t, uniqueDecodingRadius]
          rw [mul_comm]
          exact Nat.div_mul_le_self (‖C‖₀ - 1) 2
        -- Since d ≥ 2, we know d-1 < d
        have h_d_minus_1_lt_d : d - 1 < d := by
          apply Nat.sub_lt_of_pos_le
          · linarith -- d > 0
          · linarith -- 1 > 0
        -- Chain the inequalities: Δ₀(v₁, v₂) ≤ 2*t ≤ d-1 < d
        have h_dist_lt_d : Δ₀(v₁, v₂) < d := by omega
        -- By `eq_of_lt_dist`, if two codewords have a distance less than
        -- the minimum distance of the code, they must be equal.
        exact eq_of_lt_dist hv₁_mem hv₂_mem h_dist_lt_d
      · -- Case 2: d < 2 (i.e., d = 0 or d = 1)
        -- This means the code is trivial or has min distance 1
        have h_d_le_1 : d ≤ 1 := by omega
        -- If d ≤ 1, then t = ⌊(1-1)/2⌋ = 0 or ⌊(0-1)/2⌋ = 0
        have h_t_eq_0 : t = 0 := by
          dsimp only [t, d, uniqueDecodingRadius]
          apply Nat.le_zero.mp
          omega
        -- Our assumption `Δ₀(u, v₁) ≤ t` becomes `Δ₀(u, v₁) ≤ 0`
        rw [h_t_eq_0] at h_dist_v₁ h_dist_v₂
        rw [Nat.le_zero] at h_dist_v₁ h_dist_v₂
        -- If the distance is 0, the words are equal
        have h_u_eq_v1 : u = v₁ := by rw [←hammingDist_eq_zero]; exact h_dist_v₁
        have h_u_eq_v2 : u = v₂ := by rw [←hammingDist_eq_zero]; exact h_dist_v₂
        -- By transitivity, v₁ = u = v₂, so v₁ = v₂
        rw [←h_u_eq_v1, h_u_eq_v2]
    -- 5. Combine existence and uniqueness
    -- apply ExistsUnique.intro h_exists
    refine existsUnique_of_exists_of_unique h_exists ?_
    intro v₁ v₂ ⟨hv₁_mem, h_dist_v₁⟩ ⟨hv₂_mem, h_dist_v₂⟩
    exact h_uniq v₁ v₂ hv₁_mem hv₂_mem h_dist_v₁ h_dist_v₂
  · -- (←) Direction 2: "Uniquely Close" implies "Close"
    intro h_exists_unique
    rcases h_exists_unique with ⟨v, hv_mem, h_dist_le⟩
    rw [closeToCode_iff_closeToCodeword_of_minDist]
    use v

/--
A word `u` is close to a code `C` within the absolute unique decoding radius
if and only if it is close within the relative unique decoding radius.
-/
theorem UDR_close_iff_relURD_close {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] [Nonempty ι]
    (C : Set (ι → F)) (u : ι → F) :
    Δ₀(u, C) ≤ uniqueDecodingRadius C ↔ δᵣ(u, C) ≤ relativeUniqueDecodingRadius C := by
  rw [closeToCode_iff_closeToCodeword_of_minDist, relCloseToCode_iff_relCloseToCodeword_of_minDist]
  -- Goal: (∃ v ∈ C, Δ₀(u, v) ≤ t) ↔ (∃ v ∈ C, δᵣ(u, v) ≤ τ)
  apply exists_congr
  intro v
  simp only [and_congr_right_iff]
  intro hv_mem
  -- ⊢ Δ₀(u, v) ≤ t ↔ δᵣ(u, v) ≤ τ
  rw [pairRelDist_le_iff_pairDist_le]
  set n := (Fintype.card ι : NNReal)
  have h_n_pos : 0 < n := by exact NeZero.pos n
  conv_lhs => rw [uniqueDecodingRadius_eq_floor_div_2 (C := C)]
  dsimp only [relativeUniqueDecodingRadius]
  conv_rhs => rw [div_mul_cancel₀ (h := by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)]

@[simp]
theorem dist_le_UDR_iff_relDist_le_relUDR {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    [Nonempty ι] (C : Set (ι → F)) (e : ℕ) :
    e ≤ uniqueDecodingRadius C ↔
      (e : NNReal) / (Fintype.card ι : NNReal) ≤ relativeUniqueDecodingRadius C := by
    rw [uniqueDecodingRadius_eq_floor_div_2]
    unfold relativeUniqueDecodingRadius
    conv_rhs => rw [div_le_iff₀ (b := e) (c := Fintype.card ι)
      (a := ((‖C‖₀ : NNReal) - 1) / 2 / (Fintype.card ι : NNReal))
      (hc := by simp only [Nat.cast_pos, Fintype.zero_lt_card])]
    simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      IsUnit.div_mul_cancel]
    rw [Nat.le_floor_iff (ha := by simp only [zero_le])]

end DecodingRadius

end

end Code


