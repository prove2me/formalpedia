-- Prove2me | Definitions.Def_AlonMilman_PropertyT_cayleyMultigraph
-- name    : AlonMilman_PropertyT_cayleyMultigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:30:53.172366+00:00
-- url     : https://prove2.me/theorems/d3f6558b-5274-4a7f-9a35-77982cc10af2
-- title:
--   Cayley multigraph G(T, φ(S)) of a finite group with respect to the multiset φ(S)
-- statement:
--   Let $H$ be a group, $S \subseteq H$ a finite subset, $T$ a finite group and $\phi : H \to T$ a group homomorphism. Write $\phi(S) = \{\phi(s) : s \in S\}$ for the multiset of cardinality $|S|$ (an element of $T$ occurs as often as it has preimages in $S$). The **Cayley multigraph** $G = G(T, \phi(S))$ has vertex set $T$, and two vertices $w, u \in T$ are joined by
--
--   $$M_{w,u} = \#\{\, s \in S : w u^{-1} = \phi(s) \,\}$$
--
--   parallel edges. Two generators with the same image give parallel edges, and a generator in the kernel of $\phi$ gives a loop at every vertex. Every row of $M$ sums to $|S|$, so $G$ is $|S|$-regular, and $M$ is symmetric when $S = S^{-1}$.
--
--   This is the Cayley graph $G(H, \delta)$ of Alon and Milman (end of Section 3), taken with the generating multiset $\delta = \phi(S)$ as in Lemma 4.8 and Theorem 4.9.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), pp. 81–82, end of Section 3 (Cayley graph G(H, δ)); p. 85, Lemma 4.8 (φ(S) as a multiset)

import Mathlib

namespace AlonMilman.PropertyT

/-- The Cayley multigraph `G(T, φ(S))` (Alon–Milman 1985, pp. 81–82 and Lemma 4.8, p. 85) of a
finite group `T` with respect to the multiset `φ(S) = {φ(s) : s ∈ S}` of cardinality `|S|`,
where `φ : H →* T` and `S` is a finite subset of `H`: the vertices `w` and `u` are joined by as
many parallel edges as there are `s ∈ S` with `w · u⁻¹ = φ(s)`.  Entries of the multiplicity
matrix count edges; generators with the same image give parallel edges and a generator in
`ker φ` gives a loop. -/
def cayleyMultigraph {H T : Type} [Group H] [Group T] [DecidableEq T] (φ : H →* T)
    (S : Finset H) : Matrix T T ℕ :=
  fun w u => (S.filter (fun s => w * u⁻¹ = φ s)).card

end AlonMilman.PropertyT


