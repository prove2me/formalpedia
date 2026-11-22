-- Prove2me | Definitions.Def_SZ_Silver
-- name    : SZ_Silver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:42:31.932801+00:00
-- url     : https://prove2.me/theorems/1981b5e7-c61a-4df4-a4f8-61ca0b3ae875
-- title:
--   Silver
-- statement:
--   Definitions and structural lemmas for Silver, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Silver.lean

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false
namespace SZ
open Real
def pell : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * pell (n + 1) + pell n
end SZ


