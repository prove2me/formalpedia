-- Prove2me | Definitions.Def_EntropyLocalCoord_Leader_Supplement_Radius
-- name    : EntropyLocalCoord_Leader_Supplement_Radius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:36.346208+00:00
-- url     : https://prove2.me/theorems/bf944990-0620-46a2-a1a8-505f07214e5c
-- title:
--   §2, p. 6 — the radius-$r$ information skeleton $\mathfrak S(G,r)$ and $I_{\mathrm{bin}}(G,r)$, $I_{\mathrm{leader}}(G,r)$
-- statement:
--   Let $G=(N,E)$ be a finite simple graph with vertex set $N=\{1,\dots,n\}$ and let $r\ge0$ be an integer. The **radius-$r$ information skeleton** of $G$ is
--
--   $$\mathfrak S(G,r)=(N,N,B_r),\qquad B_r(i)=\{j\in N:\operatorname{dist}_G(i,j)\le r\},$$
--
--   so the information sources are the vertices themselves and player $i$ observes the sources in the ball of radius $r$ around $i$. Here $\operatorname{dist}_G$ is the shortest-path distance, which is $+\infty$ between vertices in different connected components. Every ball contains its centre, so $\mathfrak S(G,r)$ is an information skeleton.
--
--   Following the paper's abbreviation, write
--
--   $$I_{\mathrm{bin}}(G,r)=I_{\mathrm{bin}}(G,\mathfrak S(G,r)),\qquad I_{\mathrm{leader}}(G,r)=I_{\mathrm{leader}}(G,\mathfrak S(G,r)),$$
--
--   using the binary and leader inefficiencies of the mission's model definition.
--
--   This is the distance-based skeleton of range-$r$ communication in a social network on which Theorem 3.4 is stated.
--
--   **Formalization Note** The distance is Mathlib's extended graph distance `SimpleGraph.edist` with values in $\mathbb N\cup\{\infty\}$; no truncated natural-number distance is used.
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/272.pdf, SHA-256 ed0fb53954295c5258fc56b2780b62aad05401917ee1fb4064ff953d9d1d0526, §2, p. 6 (the skeleton S(G, r) and the abbreviations I(G, r), Ibin, Ileader).

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model

namespace EntropyLocalCoord.Leader.Supplement

open scoped Classical in
/-- The radius-`r` information skeleton `𝔖(G, r) = (N, N, B_r)` of a finite simple graph `G` on
`N = Fin n` (Peretz--Kraizberg, §2, p. 6): the sources are the vertices, and player `i` observes
the ball `B_r(i) = {j : dist_G(i, j) ≤ r}`. The distance is Mathlib's extended graph distance
`SimpleGraph.edist`, which is `⊤` (infinity) between vertices in different components, so only
vertices joined by a walk of length at most `r` are in the ball. Every vertex lies in its own
ball (`edist i i = 0`). -/
noncomputable def radiusSkeleton {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    InformationSkeleton n n where
  B i := Finset.univ.filter (fun j => G.edist i j ≤ (r : ℕ∞))
  nonempty i := ⟨i, by simp⟩

/-- `I_bin(G, r) := I_bin(G, 𝔖(G, r))` (§2, p. 6). -/
noncomputable def IbinR {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℝ :=
  Ibin G (radiusSkeleton G r)

/-- `I_leader(G, r) := I_leader(G, 𝔖(G, r))` (§2, p. 6). -/
noncomputable def IleaderR {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℝ :=
  Ileader G (radiusSkeleton G r)

end EntropyLocalCoord.Leader.Supplement


