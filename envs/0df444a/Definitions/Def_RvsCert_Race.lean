-- Prove2me | Definitions.Def_RvsCert_Race
-- name    : RvsCert_Race
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:19.449822+00:00
-- url     : https://prove2.me/theorems/1c016c0b-769e-4476-92a2-2228ec073921
-- title:
--   Races between countries
-- statement:
--   There are $2n$ countries $C=\{0,\dots,2n-1\}$, and a race between every two distinct countries $c\ne d$. The race $\{c,d\}$ is indexed by the pair $(c,d)$ with $c<d$, so there are $\binom{2n}{2}=n(2n-1)$ races.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.1

import Mathlib

namespace RvsCert

/-- **Races** (Section 2, p.1 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "Between each pair of distinct countries
c, d ∈ C with c ≠ d, there is a race"). Countries are `Fin (2n)`; a race `{c, d}` is indexed by
the ordered pair `(c, d)` with `c < d`, so there are `n(2n − 1)` races. -/
abbrev Race (n : ℕ) : Type := {p : Fin (2 * n) × Fin (2 * n) // p.1 < p.2}

end RvsCert


