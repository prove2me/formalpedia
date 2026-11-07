-- Prove2me | Definitions.Def_HalfIndMatch_IsInducedMatching
-- name    : HalfIndMatch_IsInducedMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:01.247204+00:00
-- url     : https://prove2.me/theorems/5a047691-3778-4e54-9ac8-d0cc9a262580
-- title:
--   Induced matchings, maximal induced matchings and the endpoint set $V(M)$
-- statement:
--   Let $G$ be a graph on the vertex set $[n]$. An **induced matching** (or strong matching) of $G$ is a set $M$ of edges of $G$ that are pairwise vertex-disjoint and such that no edge of $G$ joins an endpoint of one edge of $M$ to an endpoint of another edge of $M$; equivalently, the endpoints of $M$ span no edges of $G$ other than those of $M$. The **size** of $M$ is its number of edges $|M|$. Write $V(M)$ for the set of endpoints of $M$.
--
--   An induced matching $M$ is **maximal** if no further edge of $G$ can be added to $M$ while preserving the induced matching property: for every edge $e\notin M$ of $G$, the set $M\cup\{e\}$ is not an induced matching.
--
--   Every statement of the mission is about these objects: the maximum induced matching of $G(n,p)$ has about $L$ edges, Greedy outputs a maximal one, and online algorithms cannot exceed $(1/2+\varepsilon)L$.
--
--   **Formalization Note** Vertices are `Fin n` (the paper's $[n]$, 0-based) and edges are unordered pairs `Sym2 (Fin n)` in `G.edgeSet`. For distinct edges $e,f\in M$ and endpoints $u\in e$, $v\in f$ the definition requires $u\neq v$ and that $u,v$ are not adjacent. The module declares `vset` ($V(M)$), `IsInducedMatching` and `IsMaximalInducedMatching`.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), §1, p.1 (PDF p.3), definition of induced matching and size; §1.2, p.5 (PDF p.7), maximality

import Mathlib

open scoped Classical

namespace HalfIndMatch

/-- The endpoint set `V(M)` of a set `M` of unordered pairs of vertices of `Fin n`: the vertices
that lie in some pair of `M`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), notation
`V(M)` of §2.1, p.9 (PDF p.11).

**Formalization Note** Vertices are `Fin n`, the paper's `[n] = {1, …, n}` shifted to 0-based. -/
noncomputable def vset {n : ℕ} (M : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ e ∈ M, v ∈ e

/-- An **induced matching** (strong matching) of a graph `G` on `Fin n`: a set `M` of edges of `G`
that are pairwise vertex-disjoint and such that no edge of `G` joins an endpoint of one edge of
`M` to an endpoint of another edge of `M`. Equivalently, the endpoints of `M` span no edges of
`G` other than those of `M`. The size of `M` is its number of edges, `M.card`.

Source: arXiv:2610.40369 (held version, sha256 a1b329a1…), §1, p.1 (PDF p.3): "an induced
matching (also known as a strong matching) is a collection of vertex-disjoint edges whose
endpoints span no other edges"; "the size of a matching is its number of edges".

**Formalization Note** An edge is an unordered pair `Sym2 (Fin n)` lying in `G.edgeSet` (so it is
never a loop). For distinct `e f ∈ M` and endpoints `u ∈ e`, `v ∈ f` the definition requires
`u ≠ v` (vertex-disjointness) and `¬ G.Adj u v` (no edge between the two edges). -/
def IsInducedMatching {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ u ∈ e, ∀ v ∈ f, u ≠ v ∧ ¬ G.Adj u v

/-- A **maximal induced matching** of `G`: an induced matching `M` such that no further edge of
`G` can be added to `M` while preserving the induced matching property.

Source: arXiv:2610.40369 (held version, sha256 a1b329a1…), §1.2, p.5 (PDF p.7): "an induced
matching is maximal if no further edge can be added while preserving the induced matching
property"; §2.1, p.9 (PDF p.11). -/
def IsMaximalInducedMatching {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) :
    Prop :=
  IsInducedMatching G M ∧ ∀ e ∈ G.edgeSet, e ∉ M → ¬ IsInducedMatching G (insert e M)

end HalfIndMatch


