-- Prove2me | Definitions.Def_QGraphColl_Supplement_leviGraph
-- name    : QGraphColl_Supplement_leviGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:31:10.215271+00:00
-- url     : https://prove2.me/theorems/d4c7e3ca-91a6-4251-9986-16e4ef91453f
-- title:
--   The Levi graph $G_q$ of points and nonvertical lines of $\mathbb F_q^2$
-- statement:
--   Let $K=\mathbb F_q$ be a finite field with $q$ elements ($q$ a prime power). Let $P$ and $L$ be two disjoint copies of $K^2$: an element $(a,b)\in P$ is the **point** $(a,b)$ of the affine plane, and an element $(s,t)\in L$ is the **nonvertical line** $y=sx+t$. The point $(a,b)$ is **incident** to the line $(s,t)$ when
--   $$b=sa+t.$$
--   The **Levi graph** $G_q$ of this incidence structure is the bipartite graph with vertex set $P\sqcup L$ in which a point and a line are adjacent exactly when they are incident; there are no point–point and no line–line edges. It has $2q^2$ vertices, every vertex has degree $q$, and it has $q^3$ edges.
--
--   This is the hard family of Section 6: graph collision on $G_q$ needs $\Omega(q\sqrt{\log q})$ quantum queries (Theorem 6.1). Two points determine at most one line and two lines meet in at most one point.
--
--   **Formalization Note** The vertex type is $(K\times K)\oplus(K\times K)$, with `Sum.inl (a, b)` the point and `Sum.inr (s, t)` the line. "Let $q$ be a prime power" is encoded by taking any finite field $K$; all fields of order $q$ are isomorphic. Vertical lines are not vertices.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), §6, p.33 (definition of P, L, incidence and G_q)

import Mathlib

namespace QGraphColl.Supplement

/-- §6, p.33 of A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou,
*Breaking the quantum barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026,
sha256 21da7ff0…): incidence between a point and a nonvertical line of `𝔽_q²`. The point `(a, b)`
(`Sum.inl (a, b)`) is incident to the line `(s, t)` (`Sum.inr (s, t)`, the line `y = s·x + t`)
exactly when `b = s·a + t`; every other pair of vertices (point–point, line–line, line before
point) is not incident. -/
def incident {K : Type*} [Field K] : (K × K) ⊕ (K × K) → (K × K) ⊕ (K × K) → Prop
  | Sum.inl (a, b), Sum.inr (s, t) => b = s * a + t
  | _, _ => False

/-- §6, p.33 (Cornelissen et al., arXiv:2611.05356, version of October 2026, sha256 21da7ff0…):
the Levi graph `G_q` of the point–line incidence structure over the finite field `K = 𝔽_q`.

`P` and `L` are disjoint copies of `𝔽_q²`, representing points and nonvertical lines; the vertex
type is `(K × K) ⊕ (K × K)`, with `Sum.inl (a, b)` the point `(a, b) ∈ P` and `Sum.inr (s, t)` the
line `y = s·x + t` in `L`. There is an edge between a point and a line exactly when the point lies
on the line (`b = s·a + t`), and no other edges, so `G_q` is bipartite with sides `P` and `L`, has
`2q²` vertices, every vertex of degree `q`, and `q³` edges.

**Formalization Note.** The paper's "let `q` be a prime power" is encoded by quantifying over every
finite field `K` with `Fintype.card K = q`; all fields of order `q` are isomorphic, so this is the
same family of graphs. Vertical lines and the projective line at infinity are not vertices. -/
def leviGraph (K : Type*) [Field K] : SimpleGraph ((K × K) ⊕ (K × K)) where
  Adj u v := incident u v ∨ incident v u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by
    rcases u with ⟨a, b⟩ | ⟨s, t⟩ <;> simp [incident] at h⟩

theorem leviGraph_adj_point_line {K : Type*} [Field K] (a b s t : K) :
    (leviGraph K).Adj (Sum.inl (a, b)) (Sum.inr (s, t)) ↔ b = s * a + t := by
  simp [leviGraph, incident]

theorem leviGraph_not_adj_points {K : Type*} [Field K] (p p' : K × K) :
    ¬ (leviGraph K).Adj (Sum.inl p) (Sum.inl p') := by
  simp [leviGraph, incident]

theorem leviGraph_not_adj_lines {K : Type*} [Field K] (l l' : K × K) :
    ¬ (leviGraph K).Adj (Sum.inr l) (Sum.inr l') := by
  simp [leviGraph, incident]

end QGraphColl.Supplement


