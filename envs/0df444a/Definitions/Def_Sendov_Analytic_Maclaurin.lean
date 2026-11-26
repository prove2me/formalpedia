-- Prove2me | Definitions.Def_Sendov_Analytic_Maclaurin
-- name    : Sendov_Analytic_Maclaurin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:48:35.158132+00:00
-- url     : https://prove2.me/theorems/91963539-8c51-51fb-88f7-913696935ed7
-- title:
--   Maclaurin
-- statement:
--   Definitions and structural lemmas for Maclaurin, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Maclaurin.lean

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace Sendov
open Multiset
variable {a : ℝ} {t : Multiset ℝ}
end Sendov


