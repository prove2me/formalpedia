-- Prove2me | Definitions.Def_Sendov_Analytic_Polar
-- name    : Sendov_Analytic_Polar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:52:41.036962+00:00
-- url     : https://prove2.me/theorems/33808d61-e4fe-54e3-92ce-e7434a559f52
-- title:
--   Polar
-- statement:
--   Definitions and structural lemmas for Polar, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
set_option autoImplicit false
namespace Sendov
open Polynomial MeasureTheory
end Sendov


