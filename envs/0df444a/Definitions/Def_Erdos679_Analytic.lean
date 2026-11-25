-- Prove2me | Definitions.Def_Erdos679_Analytic
-- name    : Erdos679_Analytic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:01:16.815007+00:00
-- url     : https://prove2.me/theorems/e1ba2126-1ac0-4218-8032-b42b535de79e
-- title:
--   Analytic
-- statement:
--   Definitions and structural lemmas for Analytic, from The Erdos 679 Formalization Contributors / AItoBit (AItoBit/erdos-679-additive-refutation; see pinned Apache-2.0 LICENSE and README.md)'s pinned Refutation of the additive strengthening of Erdos Problem 679 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Filter Real
open scoped Topology
namespace Erdos679
noncomputable def primeProduct (m : ℕ) : ℕ := ∏ i ∈ Finset.range m, Nat.nth Nat.Prime i
end Erdos679


