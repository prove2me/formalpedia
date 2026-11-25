-- Prove2me | Definitions.Def_Asymptotic_CentralGrowth
-- name    : Asymptotic_CentralGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:36:41.065157+00:00
-- url     : https://prove2.me/theorems/4fa4cbac-ef08-5b71-b630-6d5dcd4bbea6
-- title:
--   Central Growth
-- statement:
--   Definitions and structural lemmas for Central Growth, from alexander (AItoBit/erdos-685-elementary-lower-bound; see pinned Apache-2.0 LICENSE and README.md)'s pinned Distinct prime divisors of central binomial coefficients (Erdos 685) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/CentralGrowth.lean

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Filter Real
open scoped Topology
namespace Erdos685Research
end Erdos685Research


