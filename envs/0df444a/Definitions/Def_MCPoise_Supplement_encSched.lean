-- Prove2me | Definitions.Def_MCPoise_Supplement_encSched
-- name    : MCPoise_Supplement_encSched
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:15:10.837198+00:00
-- url     : https://prove2.me/theorems/081de370-7ab3-44bf-8dfb-cb50c3d89cf2
-- title:
--   Binary encoding of a schedule (list of rounds of calls)
-- statement:
--   A schedule, a list of rounds each consisting of calls $(a, b)$ between vertex numbers, is written over the four-letter alphabet $\{0, 1, 2, 3\}$: the number of rounds, then for each round its number of calls followed by both endpoints of each call in binary, with the words separated by the symbol $3$.
--
--   It is the output encoding of the polynomial-time algorithms of Theorems 1.2, 1.4, 4.1 and 4.2.
--
--   **Formalization Note** Every list is length-prefixed and no word contains the separator, so the encoding is injective (checked in a sanity file).
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorems 1.2, 1.4 (p.3), 4.1, 4.2 (p.26): "polynomial time"

import Mathlib
import Definitions.Def_MCPoise_encIn

namespace MCPoise.Supplement

open OnlineCRS.Combine

/-- **Encoding of a schedule** (a list of rounds, each a list of calls `(a, b)` of vertex numbers), the output of the
machines of Theorems 1.2, 1.4, 4.1 and 4.2.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorems 1.2, 1.4 (p.3), 4.1, 4.2 (p.26): "constructed in polynomial time", "polynomial-time".

`encSched S` writes the number of rounds, then each round as its number of calls followed by both endpoints of every
call in binary (the base mission's `tokPairs`), with the words joined by the separator `3`.

**Formalization Note.** Every list is length-prefixed and no word contains `3`, so the encoding is injective
(`Solutions/verification/MCPoise_Supplement_sanity.lean`). -/
def encSched (S : List (List (ℕ × ℕ))) : List Sym :=
  EulerSparsify.joinW (ReserveLB.tokList tokPairs S)

end MCPoise.Supplement


