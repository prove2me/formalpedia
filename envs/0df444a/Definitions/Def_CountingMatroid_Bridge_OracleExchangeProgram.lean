-- Prove2me | Definitions.Def_CountingMatroid_Bridge_OracleExchangeProgram
-- name    : CountingMatroid_Bridge_OracleExchangeProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:15:50.159931+00:00
-- url     : https://prove2.me/theorems/e7cff86d-fef4-40ee-828f-13a192bd723e
-- title:
--   Fixed two-query program for matroid exchange edges
-- statement:
--   A fixed Arlib-free register-machine program tests both candidate independence-oracle queries for a directed matroid-intersection exchange edge. It makes exactly two oracle calls for every pair of one-bit orientation guards, ignores invalid orientations, and returns true precisely when an enabled candidate is independent.
-- source:
--   Lean 4.33.1 formalization for the existing Approximate counting of common bases of two matroids mission. The program uses the mission oracle instruction directly and does not depend on Arlib.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open OAI.CommonBasesFPRAS

/-- Two guarded independence-oracle tests. The control flow always performs
both calls, ignores answers for invalid orientations, and reaches state 12
exactly when at least one enabled candidate is accepted. -/
def oracleExchangeEdgeProgram : Program 2 16 := fun pc =>
  match pc.val with
  | 0 => .pop ⟨6, by omega⟩ ⟨11, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
  | 1 => .pop ⟨7, by omega⟩ ⟨11, by omega⟩ ⟨3, by omega⟩ ⟨4, by omega⟩
  | 2 => .pop ⟨7, by omega⟩ ⟨11, by omega⟩ ⟨5, by omega⟩ ⟨6, by omega⟩
  | 3 => .query false ⟨8, by omega⟩ ⟨7, by omega⟩ ⟨7, by omega⟩
  | 4 => .query false ⟨8, by omega⟩ ⟨8, by omega⟩ ⟨8, by omega⟩
  | 5 => .query false ⟨8, by omega⟩ ⟨13, by omega⟩ ⟨14, by omega⟩
  | 6 => .query false ⟨8, by omega⟩ ⟨15, by omega⟩ ⟨16, by omega⟩
  | 7 => .query true ⟨9, by omega⟩ ⟨10, by omega⟩ ⟨10, by omega⟩
  | 8 => .query true ⟨9, by omega⟩ ⟨10, by omega⟩ ⟨12, by omega⟩
  | 9 => .query true ⟨9, by omega⟩ ⟨10, by omega⟩ ⟨10, by omega⟩
  | 10 => .halt
  | 11 => .halt
  | 12 => .halt
  | 13 => .query true ⟨9, by omega⟩ ⟨10, by omega⟩ ⟨10, by omega⟩
  | 14 => .query true ⟨9, by omega⟩ ⟨12, by omega⟩ ⟨12, by omega⟩
  | 15 => .query true ⟨9, by omega⟩ ⟨10, by omega⟩ ⟨12, by omega⟩
  | 16 => .query true ⟨9, by omega⟩ ⟨12, by omega⟩ ⟨12, by omega⟩
  | _ => .halt

end CountingMatroid.Bridge


