-- Prove2me | Definitions.Def_GeoSemialgCSP_cousinsW
-- name    : GeoSemialgCSP_cousinsW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:46.418394+00:00
-- url     : https://prove2.me/theorems/313a7aec-aad9-4767-9030-e3bf29e310ca
-- title:
--   Cousins among leaves of the complete tree $T_m$
-- statement:
--   Let $T_m$ be the complete ordered $k$-ary tree of height $h$, with $m=k^h$ leaves. Its leaves are the words of length $h$ over $\{0,\dots,k-1\}$ (root-to-leaf paths). Leaves $l_1,\dots,l_k$ are cousins if, for some position $p$, all words agree before $p$ and word $l_i$ has letter $i$ at position $p$.
--
--   **Formalization Note** The paper numbers the leaves $0,\dots,m-1$ from left to right; the number of a leaf is the base-$k$ value of its word.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_GeoSemialgCSP_cousins

namespace GeoSemialgCSP

/-- **Cousins among leaves of the complete tree `T_m`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.1, printed
p.10 (PDF p.11): `T_m` is the complete ordered `k`-ary tree of height `h`, with `m = k^h` leaves.

**Formalization Note.** The leaves of `T_m` are the words `Fin h → Fin k` (root-to-leaf paths);
the paper's left-to-right leaf number is the word's base-`k` value. The predicate is `cousins`
of the words read as lists. -/
def cousinsW {k h : ℕ} (l : Fin k → (Fin h → Fin k)) : Prop :=
  cousins (fun i => List.ofFn (l i))

end GeoSemialgCSP


