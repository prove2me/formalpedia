-- Prove2me | Definitions.Def_Erdos684_Analytic
-- name    : Erdos684_Analytic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:10:20.256804+00:00
-- url     : https://prove2.me/theorems/c4fe865b-74d0-4702-a358-1d34725fd8bf
-- title:
--   Analytic
-- statement:
--   Definitions and structural lemmas for Analytic, from AItoBit (AItoBit/erdos-684-elementary-bounds; see pinned Apache-2.0 LICENSE and README.md)'s pinned Elementary upper and lower bounds for Erdos Problem 684 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Analytic.lean

module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
@[expose] public section
open Filter Real
open scoped Topology
@[expose] public section
namespace Erdos684
noncomputable def primeCutoff (n : ℕ) : ℕ := Nat.ceil (256 * (log (n : ℝ)) ^ 2)
noncomputable def windowLength (n : ℕ) : ℕ := Nat.ceil (32 * log (n : ℝ))
end Erdos684


