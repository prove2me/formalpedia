-- Prove2me | Definitions.Def_QuarterSumLadder_Prelim
-- name    : QuarterSumLadder_Prelim
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:55:04.388011+00:00
-- url     : https://prove2.me/theorems/43b5fdef-edab-5799-99e9-a5c0e4a2f914
-- title:
--   Prelim
-- statement:
--   Definitions and structural lemmas for Prelim, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Prelim.lean

module
public import Definitions.Def_QuarterSumLadder_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
def gaussMap (x : ZMod p) : ZMod p := if 4 * x.val < p then 2 * x else -(2 * x)
end QuarterSumLadder


