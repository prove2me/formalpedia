-- Prove2me | Definitions.Def_SATotalCoeffLB_Pair
-- name    : SATotalCoeffLB_Pair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:54.052406+00:00
-- url     : https://prove2.me/theorems/55120108-29af-4dda-8978-4e05ee5897b4
-- title:
--   Pairs $i<j$: the index set $\binom{[n]}{2}$
-- statement:
--   For $n \ge 0$, $\binom{[n]}{2}$ is the set of pairs $e = \{i, j\}$ of distinct elements of $[n]$, written with $i < j$. The paper indexes the AND variables $Y_{ij}$, the AND checks $p_{ij}$ and the edges of the graph $E$ of Section 9.1 by these pairs, and writes $e = \{i,j\}$ and $ij$ interchangeably.
--
--   **Formalization Note** Vertices are $0, \dots, n-1$. A pair is stored as the ordered pair $(i,j)$ together with a proof of $i<j$, so a set of pairs is automatically a graph without loops or repeated edges.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (AND gate checks) and Section 9, p.48

import Mathlib

namespace SATotalCoeffLB

/-- **Pairs `i < j`**, the index set `([n] choose 2)` of the AND variables `Y_ij` (p.9; Section 9,
p.48, "a pair e = {i, j} with i < j"), from Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

**Formalization Note** Vertices are `Fin n` (0-based). A pair `e = {i, j}` with `i < j` is stored as
the ordered pair `(i, j)` with the proof `i < j`, so loops and repeated pairs are excluded by the
type. -/
abbrev Pair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

end SATotalCoeffLB


