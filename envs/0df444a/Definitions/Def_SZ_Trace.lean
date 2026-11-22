-- Prove2me | Definitions.Def_SZ_Trace
-- name    : SZ_Trace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:41:00.395855+00:00
-- url     : https://prove2.me/theorems/86e5d626-02eb-4763-b33f-db5466c2abd0
-- title:
--   Trace
-- statement:
--   Definitions and structural lemmas for Trace, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
namespace SZ
def rec2 (A B t₀ t₁ : ℤ) : ℕ → ℤ
  | 0 => t₀
  | 1 => t₁
  | (n + 2) => A * rec2 A B t₀ t₁ (n + 1) + B * rec2 A B t₀ t₁ n
end SZ


