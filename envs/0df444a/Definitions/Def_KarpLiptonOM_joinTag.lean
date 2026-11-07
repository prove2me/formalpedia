-- Prove2me | Definitions.Def_KarpLiptonOM_joinTag
-- name    : KarpLiptonOM_joinTag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:13.221201+00:00
-- url     : https://prove2.me/theorems/386e96d2-9774-4cd6-994d-746e6c35c63f
-- title:
--   Fixed-width tag of an index $i < r$
-- statement:
--   In the join of $r$ promise problems, the index $i$ of a component is written with a fixed number of bits in front of the query. Here the tag of $i \in \{0, \dots, r-1\}$ is its one-hot code of width $r$: the string whose $j$-th bit is $1$ exactly when $j = i$.
--
--   **Formalization Note** Any fixed-width injective code would do; one-hot has width $r$, constant for a fixed join.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (Π₁⊕⋯⊕Π_r)

import Mathlib

namespace KarpLiptonOM

/-- The fixed-width tag of the index `i` in the join `Π₁ ⊕ ⋯ ⊕ Π_r` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21: "where
`i` is written with a fixed number of bits").

**Formalization Note** The tag is the one-hot code of `i` of width `r` (bit `j` is `1` iff `j = i`,
indices from `0`). -/
def joinTag (r : ℕ) (i : Fin r) : List Bool := List.ofFn (fun j : Fin r => decide (j = i))

end KarpLiptonOM


