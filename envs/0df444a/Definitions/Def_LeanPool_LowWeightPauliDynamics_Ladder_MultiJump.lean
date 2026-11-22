-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
-- name    : LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:46.276393+00:00
-- url     : https://prove2.me/theorems/e3d4e7f2-d19d-4e41-bc34-0946806fa76a
-- title:
--   Multi Jump
-- statement:
--   Definitions and structural lemmas for Multi Jump, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
def chain (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, m => E m
  | (k + 2), m => ∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j)
@[simp] lemma chain_zero (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (m : ℕ) : chain eps E 0 m = 0 := rfl
@[simp] lemma chain_one (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (m : ℕ) : chain eps E 1 m = E m := rfl
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}
structure MultiLadder (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (M : ℝ) where
  /-- Mass strictly above rung `m` after `T` layers. -/
  N : ℕ → ℕ → ℝ
  nonneg : ∀ m T, 0 ≤ N m T
  init : ∀ m, 1 ≤ m → N m 0 = 0
  step : ∀ m T, 1 ≤ m →
    N m (T + 1) ≤ N m T + (∑ j ∈ Ico 1 m, eps j m * N (m - j) T) + E m * M
namespace MultiLadder
variable {M : ℝ}
noncomputable def majorant (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (M : ℝ) (m T : ℕ) : ℝ :=
  M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}
def trivialMultiLadder {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
    (_heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) : MultiLadder eps E M where
  N _ _ := 0
  nonneg _ _ := le_refl 0
  init _ _ := rfl
  step m T _ := by
    have h1 : (0 : ℝ) ≤ ∑ j ∈ Ico 1 m, eps j m * 0 := by
      exact Finset.sum_nonneg fun j _ => by simp
    have h2 : (0 : ℝ) ≤ E m * M := mul_nonneg (hE m) hM
    simpa using by linarith [h1, h2]
end MultiLadder
end Lean4LPD


