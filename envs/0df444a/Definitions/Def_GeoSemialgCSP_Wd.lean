-- Prove2me | Definitions.Def_GeoSemialgCSP_Wd
-- name    : GeoSemialgCSP_Wd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:03.88684+00:00
-- url     : https://prove2.me/theorems/166db79b-ac05-40d4-aa19-44a82c998580
-- title:
--   The leaves $[M]$ of $T_M$
-- statement:
--   For $M=k^H$, the set $[M]$ is identified with the leaves of the complete ordered $k$-ary tree $T_M$ of height $H$, i.e. with the words of length $H$ over $\{0,\dots,k-1\}$.
--
--   The variables of the dictatorship test are the vectors in $[M]^R$.
--
--   **Formalization Note** The number of a leaf is the base-$k$ value of its word.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.2, p.10 (PDF p.11)

import Mathlib

namespace GeoSemialgCSP

/-- **The leaves `[M]` of `T_M`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.2, printed p.10 (PDF p.11): `M = k^H` is a
power of `k`, and `[M]` is identified with the leaves of the complete ordered `k`-ary tree `T_M`
of height `H`.

**Formalization Note.** `[M]` is the set of words `Fin H → Fin k`; the paper's leaf number is the
base-`k` value of the word. -/
abbrev Wd (k H : ℕ) : Type := Fin H → Fin k

end GeoSemialgCSP


