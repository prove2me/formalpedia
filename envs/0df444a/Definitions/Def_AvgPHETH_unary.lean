-- Prove2me | Definitions.Def_AvgPHETH_unary
-- name    : AvgPHETH_unary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:35.520195+00:00
-- url     : https://prove2.me/theorems/5fca753b-fd8a-4d0b-8ebb-ae20f14992db
-- title:
--   The tally string $1^n$
-- statement:
--   The string $1^n$ consisting of $n$ ones, used to give a machine the parameter $n$ in unary.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16)

import Mathlib

namespace AvgPHETH

/-- The tally string `1^n` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16)). -/
def unary (n : ℕ) : List Bool := List.replicate n true

end AvgPHETH


