-- Prove2me | Definitions.Def_OrderedExperts_pathFlow
-- name    : OrderedExperts_pathFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:37.063696+00:00
-- url     : https://prove2.me/theorems/cffe9d2d-466a-49e2-85db-4d93b8cc991d
-- title:
--   Edge-use probability of the random path
-- statement:
--   For a target rank $j$, the **edge-use probability** of an edge $(a,b)$ is the probability that the random increasing path from the anchor to $j$ jumps directly from $a$ to $b$:
--   $$
--   \varphi_j(a,b)=r_j(a)\,\frac{\pi(b)}{\Pi(a,j]}\qquad(0\le a<b\le j),
--   $$
--   and $\varphi_j(a,b)=0$ for every other pair. Here $r_j$ is the reach probability. Because the path visits each node at most once, this is exactly the probability that the path traverses the edge.
--
--   This is the probabilistic definition of the flows; Lemma 7 computes them in closed form.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.2, p.7; Sec. 3.3, p.8

import Definitions.Def_OrderedExperts_massOC
import Definitions.Def_OrderedExperts_reach

namespace OrderedExperts

/-- **Edge-use probability of the random path.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.2, p.7:
"For a target rank `j`, let a random increasing path run from the anchor to `j`, jumping from each rank
`a < j` to some rank `b ∈ {a + 1, . . . , j}`, and let `φj(e)` be the probability that it traverses the
edge `e`." The law of the path is that of Sec. 3.3, p.8 (`P(b | a, j) = π(b)/Π(a, j]`).

`pathFlow π j a b` is the probability that the path towards `j` jumps directly from `a` to `b`: the
probability `reach π j a` that it visits `a`, times the next-step probability `π(b)/Π(a, j]`, for
`a < b ≤ j`, and `0` for every other pair. Since the path is strictly increasing it visits each node
at most once, so this is exactly the probability that it traverses the edge `(a, b)`.

**Formalization Note.** This is the probabilistic definition, not the closed form; Lemma 7
(`OrderedExperts.lemma_7`) computes it. -/
noncomputable def pathFlow (π : ℕ → ℝ) (j a b : ℕ) : ℝ :=
  if a < b ∧ b ≤ j then reach π j a * (π b / massOC π a j) else 0

end OrderedExperts


