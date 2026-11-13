-- Prove2me | Definitions.Def_RvsCert_TPair
-- name    : RvsCert_TPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:17.149582+00:00
-- url     : https://prove2.me/theorems/4815afb4-ac96-4aff-b07f-eaec0df8afc8
-- title:
--   Input bits of a tournament on $m$ vertices
-- statement:
--   A tournament on the vertex set $\{0,\dots,m-1\}$ is given by one bit for each unordered pair $\{u,v\}$ of distinct vertices, $\binom m2$ bits in total. The bit of the pair is indexed by $(u,v)$ with $u<v$. This is the input of the SINK and king-finding problems in Section 3.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 3, p.4

import Mathlib

namespace RvsCert

/-- **Input bits of a tournament** (Section 3, p.4 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "the input is an
orientation of the complete graph on n vertices, turning each of the (n choose 2) edges into a
directed arc (using (n choose 2) input bits)"): one bit per unordered pair `{u, v}` of vertices of
`Fin m`, indexed by the ordered pair `(u, v)` with `u < v`. -/
abbrev TPair (m : ℕ) : Type := {p : Fin m × Fin m // p.1 < p.2}

end RvsCert


