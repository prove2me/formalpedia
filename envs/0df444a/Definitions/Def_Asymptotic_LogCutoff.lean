-- Prove2me | Definitions.Def_Asymptotic_LogCutoff
-- name    : Asymptotic_LogCutoff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:36:35.487213+00:00
-- url     : https://prove2.me/theorems/6484f2be-bdfc-5068-8c2e-b48884a210ea
-- title:
--   Log Cutoff
-- statement:
--   Definitions and structural lemmas for Log Cutoff, from alexander (AItoBit/erdos-685-elementary-lower-bound; see pinned Apache-2.0 LICENSE and README.md)'s pinned Distinct prime divisors of central binomial coefficients (Erdos 685) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/LogCutoff.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Filter Real
open scoped Topology
namespace Erdos685Research
noncomputable def cutoff (n : ℕ) : ℝ := (n : ℝ) / Real.log n ^ 2
end Erdos685Research


