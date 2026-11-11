-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Splitting
-- name    : FracColorLocal_KrFree_Splitting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:32.974792+00:00
-- url     : https://prove2.me/theorems/4c2432b1-7397-4751-a9f0-3e7032cee33e
-- title:
--   Deletion and splitting: a graph G′ with a projection σ that is a homomorphism injective on edges
-- statement:
--   A **vertex splitting** partitions the edges at a vertex into groups and replaces the vertex by one copy per group; each copy inherits its parent's weight and parameter. Combined with deletions of edges and vertices, a sequence of such operations turns $G$ into a graph $G'$ together with a map $\sigma:V(G')\to V(G)$ sending each vertex to its original vertex, such that
--
--   $$ab\in E(G')\ \Rightarrow\ \sigma(a)\sigma(b)\in E(G),\qquad\text{and distinct edges of }G'\text{ map to distinct edges of }G.$$
--
--   Weights and parameters are inherited: $w'=w\circ\sigma$, $\theta'=\theta\circ\sigma$. Thus every surviving edge or triangle of $G'$ corresponds to a distinct original edge or triangle of the same weight.
--
--   **Formalization Note** `IsDeletionSplitting G G' σ` is exactly the two displayed conditions (unordered edges compared as `Sym2` pairs). Copies of one vertex are never adjacent (an edge between them would map to a loop). Inheritance of weights is written as `w ∘ σ`, `θ ∘ σ` where the relation is used (Lemma 8.1).
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 33 (PDF 34), §8 and §8.1

import Mathlib

namespace FracColorLocal.KrFree

/-- `G'` is obtained from `G` by deleting edges and vertices and splitting vertices (§8, §8.1),
with `σ : V' → V` sending every vertex of `G'` to its original vertex: `σ` maps every edge of `G'`
to an edge of `G`, and distinct edges of `G'` to distinct edges of `G`. Weights and parameters are
inherited along `σ` (`w ∘ σ`, `θ ∘ σ`) where this relation is used. -/
def IsDeletionSplitting {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') (σ : V' → V) :
    Prop :=
  (∀ a b, G'.Adj a b → G.Adj (σ a) (σ b)) ∧
    ∀ a b c d, G'.Adj a b → G'.Adj c d → s(σ a, σ b) = s(σ c, σ d) → s(a, b) = s(c, d)

end FracColorLocal.KrFree


