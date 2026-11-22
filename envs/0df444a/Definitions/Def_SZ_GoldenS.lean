-- Prove2me | Definitions.Def_SZ_GoldenS
-- name    : SZ_GoldenS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:41:09.714139+00:00
-- url     : https://prove2.me/theorems/5acf36be-e052-41e4-bfed-c06c03b685ac
-- title:
--   Golden S
-- statement:
--   Definitions and structural lemmas for Golden S, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/GoldenS.lean

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
set_option autoImplicit false
namespace SZ
open Real
noncomputable def golden : ℝ := (1 + Real.sqrt 5) / 2
end SZ


