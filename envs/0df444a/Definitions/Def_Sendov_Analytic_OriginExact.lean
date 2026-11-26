-- Prove2me | Definitions.Def_Sendov_Analytic_OriginExact
-- name    : Sendov_Analytic_OriginExact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:56:03.603359+00:00
-- url     : https://prove2.me/theorems/1236b451-c088-4542-b656-bf5338d3e2ea
-- title:
--   Origin Exact
-- statement:
--   Definitions and structural lemmas for Origin Exact, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
set_option autoImplicit false
namespace Sendov
open Complex (I)
noncomputable def Worigin (n : ℕ) (a x y : ℝ) : ℂ :=
  (a : ℂ) ^ 2 * ((n : ℂ) - 1) + 1 - (a : ℂ) * ((x : ℂ) + (y : ℂ) * I)
end Sendov


