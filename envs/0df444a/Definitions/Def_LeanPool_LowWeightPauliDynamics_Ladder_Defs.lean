-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
-- name    : LeanPool_LowWeightPauliDynamics_Ladder_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:48.970586+00:00
-- url     : https://prove2.me/theorems/674f9159-f019-4625-8685-a9ed89150755
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Defs.lean

module
public import Mathlib.Data.Real.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
def rungWeight (ko kh m : ℕ) : ℕ := ko + (m - 1) * (kh - 1)
structure Ladder (a M : ℝ) where
  /-- Mass strictly above rung `m` after `g` steps. -/
  N : ℕ → ℕ → ℝ
  nonneg : ∀ m g, 0 ≤ N m g
  reservoir : ∀ g, N 0 g ≤ M
  init : ∀ m, 1 ≤ m → N m 0 = 0
  step : ∀ m g, 1 ≤ m → N m (g + 1) ≤ N m g + a * N (m - 1) g
end Lean4LPD


