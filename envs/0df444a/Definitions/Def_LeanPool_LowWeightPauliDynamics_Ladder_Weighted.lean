-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
-- name    : LeanPool_LowWeightPauliDynamics_Ladder_Weighted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:58:07.0248+00:00
-- url     : https://prove2.me/theorems/49329c63-b653-44a8-84e8-412eeb86d3e9
-- title:
--   Weighted
-- statement:
--   Definitions and structural lemmas for Weighted, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
structure WeightedLadder (c : ℕ → ℝ) (M : ℝ) where
  /-- Mass strictly above rung `m` after `g` steps. -/
  N : ℕ → ℕ → ℝ
  nonneg : ∀ m g, 0 ≤ N m g
  reservoir : ∀ g, N 0 g ≤ M
  init : ∀ m, 1 ≤ m → N m 0 = 0
  step : ∀ m g, 1 ≤ m → N m (g + 1) ≤ N m g + c m * N (m - 1) g
namespace WeightedLadder
variable {c : ℕ → ℝ} {M : ℝ} (L : WeightedLadder c M)
end WeightedLadder
noncomputable def satLadder {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, 0 ≤ c j) (hM : 0 ≤ M) :
    WeightedLadder c M where
  N m g := (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M
  nonneg m g := by
    have : (0 : ℝ) ≤ ∏ j ∈ Icc 1 m, c j := Finset.prod_nonneg fun j _ => hc j
    positivity
  reservoir g := by simp
  init m hm := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  step m g hm := by
    match m with
    | 0 => omega
    | (m + 1) =>
      have hprod : ∏ j ∈ Icc 1 (m + 1), c j = (∏ j ∈ Icc 1 m, c j) * c (m + 1) :=
        Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) c
      have hpascal : ((g + 1).choose (m + 1) : ℝ) = (g.choose m : ℝ) + (g.choose (m + 1) : ℝ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      simp only [Nat.add_sub_cancel]
      rw [hprod, hpascal]
      ring_nf
      exact le_refl _
end Lean4LPD


