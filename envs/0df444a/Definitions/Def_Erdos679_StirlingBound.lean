-- Prove2me | Definitions.Def_Erdos679_StirlingBound
-- name    : Erdos679_StirlingBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:50:40.219958+00:00
-- url     : https://prove2.me/theorems/17de164d-72f2-4263-927e-d4510b5f9aaa
-- title:
--   Stirling Bound
-- statement:
--   Definitions and structural lemmas for Stirling Bound, from The Erdos 679 Formalization Contributors / AItoBit (AItoBit/erdos-679-additive-refutation; see pinned Apache-2.0 LICENSE and README.md)'s pinned Refutation of the additive strengthening of Erdos Problem 679 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/StirlingBound.lean

module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Filter Real
open scoped Topology
namespace Erdos679
end Erdos679


