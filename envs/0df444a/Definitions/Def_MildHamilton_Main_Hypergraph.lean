-- Prove2me | Definitions.Def_MildHamilton_Main_Hypergraph
-- name    : MildHamilton_Main_Hypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:04.893865+00:00
-- url     : https://prove2.me/theorems/6f3616f7-1d56-4c99-9e23-5412c4171bc2
-- title:
--   Bipartite hypergraphs, $\tau(\mathcal H_S)$ and saturating matchings
-- statement:
--   A **bipartite hypergraph** with vertex partition $A\cup B$ here has edges meeting $A$ in exactly one vertex. For $S\subseteq A$, the hypergraph $\mathcal H_S$ on $B$ has edge set
--
--   $$E(\mathcal H_S) = \{e\cap B : e\in E(\mathcal H),\ e\cap S\ne\varnothing\},$$
--
--   and $\tau(\mathcal F)$ is the minimum number of vertices meeting every edge of $\mathcal F$. A **matching saturating $A$** is a family of pairwise disjoint edges covering $A$.
--
--   These are the objects of Haxell's matching theorem, which turns a vertex-cover bound into disjoint connecting paths.
--
--   **Formalization Note** An edge $e$ is recorded as the pair $(a, e\cap B)$ with $e\cap A=\{a\}$, which determines $e$. The inequality $\tau(\mathcal F)>x$ is rendered as "no set of at most $x$ vertices meets every edge". This covers a family containing the empty edge, which has no cover, so that $\tau=\infty$ there.
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Theorem 3.2, p. 6

import Mathlib

namespace MildHamilton.Main

/-- A finite bipartite hypergraph with vertex partition `A ∪ B` in which every edge meets `A` in exactly one
vertex (Muyesser, STOC 2027 submission #233, Theorem 3.2, p. 6). The edge `e` is recorded as the pair
`(a, e ∩ B)`, where `e ∩ A = {a}`; this determines `e`. -/
structure BipartiteHypergraph (A B : Type*) where
  /-- The edges, as pairs `(a, e ∩ B)`. -/
  edges : Finset (A × Finset B)

open Classical in
/-- The edge set `E(H_S) = {e ∩ B : e ∈ E(H), e ∩ S ≠ ∅}` of the hypergraph `H_S` on `B`. -/
noncomputable def BipartiteHypergraph.link {A B : Type*} (H : BipartiteHypergraph A B)
    (S : Finset A) : Finset (Finset B) :=
  (H.edges.filter fun e => e.1 ∈ S).image Prod.snd

/-- `U` is a vertex cover of the family `F`: it meets every member of `F`. -/
def IsVertexCover {B : Type*} (F : Finset (Finset B)) (U : Finset B) : Prop :=
  ∀ f ∈ F, ¬ Disjoint f U

/-- `τ(F) > x`, where `τ(F)` is the minimum number of vertices meeting every edge of `F`: no set of at
most `x` vertices is a vertex cover. A family with an empty edge has no cover, so `τ = ∞` there and the
inequality holds for every `x`. -/
def TauGreaterThan {B : Type*} (F : Finset (Finset B)) (x : ℤ) : Prop :=
  ∀ U : Finset B, (U.card : ℤ) ≤ x → ¬ IsVertexCover F U

/-- `H` has a matching saturating `A`: a choice, for every `a`, of an edge through `a`, the chosen edges
being pairwise disjoint. Disjointness on the `A` side is automatic. -/
def BipartiteHypergraph.HasSaturatingMatching {A B : Type*} (H : BipartiteHypergraph A B) : Prop :=
  ∃ f : A → Finset B, (∀ a, (a, f a) ∈ H.edges) ∧
    ∀ a a', a ≠ a' → Disjoint (f a) (f a')

end MildHamilton.Main


