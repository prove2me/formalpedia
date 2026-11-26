-- Prove2me | Definitions.Def_QuadraticFloor_CoefficientFive
-- name    : QuadraticFloor_CoefficientFive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:46:44.946925+00:00
-- url     : https://prove2.me/theorems/401d6cf5-a465-48ca-82db-628829b62ff8
-- title:
--   Coefficient Five
-- statement:
--   Definitions and structural lemmas for Coefficient Five, from J. S. Farland (jkfarland-bot/QuadraticFloor; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuadraticFloor: quadratic floor sums and the trace of a quartic Bernoulli number development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean

module
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuadraticFloor
open Finset
instance fact_one_lt_five : Fact (1 < 5) := ⟨by norm_num⟩
variable {p : ℕ} [hp : Fact p.Prime]
end QuadraticFloor


