-- Prove2me | Definitions.Def_Asymptotic_CentralAsymptotic
-- name    : Asymptotic_CentralAsymptotic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:41:31.799983+00:00
-- url     : https://prove2.me/theorems/ee9fb340-f2cd-45dc-8d43-939f13ee828f
-- title:
--   Central Asymptotic
-- statement:
--   Definitions and structural lemmas for Central Asymptotic, from alexander (AItoBit/erdos-685-elementary-lower-bound; see pinned Apache-2.0 LICENSE and README.md)'s pinned Distinct prime divisors of central binomial coefficients (Erdos 685) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/CentralAsymptotic.lean

module
public import Definitions.Def_Asymptotic_CentralGrowth
public import Definitions.Def_Asymptotic_PrimeCutoff
public import Definitions.Def_Asymptotic_LogCutoff
public import Definitions.Def_Erdos685ElementaryLowerBound_Solution
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Filter Real Finset
open scoped Topology ArithmeticFunction.omega
namespace Erdos685Research
end Erdos685Research


