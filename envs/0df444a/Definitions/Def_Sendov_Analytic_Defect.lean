-- Prove2me | Definitions.Def_Sendov_Analytic_Defect
-- name    : Sendov_Analytic_Defect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:49:11.173161+00:00
-- url     : https://prove2.me/theorems/e6021dd2-60bc-5472-905a-b483e6b74bff
-- title:
--   Defect
-- statement:
--   Definitions and structural lemmas for Defect, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Defect.lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace Sendov
open Multiset
end Sendov


