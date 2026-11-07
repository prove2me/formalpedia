-- Prove2me | Definitions.Def_UniqueOptScores_decodeNat
-- name    : UniqueOptScores_decodeNat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:50.107887+00:00
-- url     : https://prove2.me/theorems/fefea6a3-78b0-4e2a-a2e7-e7038efaabbb
-- title:
--   Reading an output word as a score
-- statement:
--   Scores are natural numbers written by an evaluator on its output tape. The word $b_0b_1\cdots b_m$ is read in binary, least significant bit first:
--   $$
--   \mathrm{num}(b_0b_1\cdots b_m) = \sum_{i=0}^{m} b_i\,2^i ,\qquad \mathrm{num}(\varepsilon) = 0 .
--   $$
--   Every word denotes a number, so no output is malformed; values above the allowed score range are replaced by $0$ (see the score of a candidate).
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Definition 4.1, p.16

import Mathlib

namespace UniqueOptScores

/-- **Reading a machine's output as a natural number (a score).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Definition 4.1, p.16: scores `s^A(x, z) ∈ {0, …, k}`.

The word `b₀ b₁ … b_m` is read in binary, least significant bit first:
`decodeNat (b :: l) = b + 2 · decodeNat l`, `decodeNat [] = 0`.

**Formalization Note.** The decoder is total, so no output is malformed; out-of-range values are
replaced by zero in `score`. -/
def decodeNat : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * decodeNat l

end UniqueOptScores


