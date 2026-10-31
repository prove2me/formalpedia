-- Prove2me | Definitions.Def_FastCore_Phase
-- name    : FastCore_Phase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:46.183506+00:00
-- url     : https://prove2.me/theorems/e30d5809-5450-4355-aed8-620cebc2dd9d
-- title:
--   Control location of Algorithm 1
-- statement:
--   A run of Algorithm 1 is at one of three control locations: the `while` loop of Algorithm 1 (lines 3–6), the `while` loop of the subroutine Core-Search (Procedure 2), or the return.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1 and Procedure 2, pp.15–16

import Mathlib

namespace FastCore

/-- The control location of a run of Algorithm 1 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1 and Procedure 2, pp.15–16):
`outer` is the `while` of Algorithm 1 (lines 3–6), `search` is the `while` of Core-Search, and
`done` is the return. -/
inductive Phase
  | outer
  | search
  | done
  deriving DecidableEq

end FastCore


