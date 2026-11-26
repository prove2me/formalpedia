-- Prove2me | Definitions.Def_Sendov_Interior
-- name    : Sendov_Interior
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T20:04:00.049731+00:00
-- url     : https://prove2.me/theorems/7496cccf-7d50-565e-867c-34ee4a88f622
-- title:
--   Interior
-- statement:
--   Definitions and structural lemmas for Interior, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Interior.lean

import Definitions.Def_Sendov_Analytic_OriginExact
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Reduction_Main
set_option autoImplicit false
namespace Sendov
open Polynomial
open Complex (I)
end Sendov


