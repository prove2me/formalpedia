-- Prove2me | Definitions.Def_AvgPHETH_binTuple
-- name    : AvgPHETH_binTuple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:50.5152+00:00
-- url     : https://prove2.me/theorems/b19f96fa-40c7-4d75-9791-ac7dba613e79
-- title:
--   The fixed binary encoding of a tuple of strings
-- statement:
--   The fixed encoding of a tuple $(z_1,\dots,z_q)$ as one binary string: each bit of $z_i$ is doubled and each component ends with $01$. The encoding is injective, the number of components included, and the empty tuple is the empty string, so that the conditional $K^{t,O}(z_i\mid z_1,\dots,z_{i-1})$ at $i=1$ is the unconditional complexity.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.18 (PDF 20)

import Mathlib

namespace AvgPHETH

/-- The fixed binary encoding of a tuple of strings (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.18 (PDF 20): "a fixed encoding of
the tuple `(z₁, …, z_q)`").

**Formalization Note** Each bit of a component is doubled and each component ends with `01`, so the
encoding is injective on all lists, the number of components included, and `binTuple [] = []` is the
empty string, the omitted condition of `K^{t,O}(z)`. The published `tupleEnc` is over `{0, 1, #}`
and identifies `[]` with `[[]]`, so it cannot be a target or output of `U`. -/
def binTuple (l : List (List Bool)) : List Bool :=
  l.flatMap (fun u => u.flatMap (fun b => [b, b]) ++ [false, true])

end AvgPHETH


