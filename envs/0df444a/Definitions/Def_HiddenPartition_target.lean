-- Prove2me | Definitions.Def_HiddenPartition_target
-- name    : HiddenPartition_target
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:27.381527+00:00
-- url     : https://prove2.me/theorems/33cb4395-a7e6-471b-b834-b179f070822d
-- title:
--   Copy maps $\phi_a$, images $W_a$ and the target graph $Z$
-- statement:
--   Let $G$ be a graph with domains $\mathrm{dom}:V(G)\to[k]$, let $A,B$ be finite sets and let $\mathcal F=\{f_v:A\to B\}_{v\in V(G)}$ be a family of maps. Each $a\in A$ is a **seed**. For a seed $a$,
--
--   $$\phi_a(v)=(\mathrm{dom}(v),f_v(a)),\qquad W_a=\phi_a(V(G)).$$
--
--   The **target graph** $Z$ has vertex set $[k]\times B$ and edge set
--
--   $$E(Z)=\bigcup_{a\in A}\bigl\{\{\phi_a(u),\phi_a(v)\}:\{u,v\}\in E(G)\bigr\},$$
--
--   so two target vertices are adjacent when some seed maps an edge of $G$ onto them. Each $Z[W_a]$ is meant to be a copy of $G$; the construction depends only on $G$ and the domains.
--
--   **Formalization Note** Domains are `Fin k`. The adjacency also requires the two target vertices to be distinct, which keeps $Z$ loopless for every family; when every $\phi_a$ is injective (copy injectivity) this condition is automatic, so $Z$ is the paper's graph.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), §3.1, pp.12–13 (pdf pp.14–15)

import Mathlib

set_option autoImplicit false

namespace HiddenPartition

/-- The copy map `ϕ_a(v) = (dom(v), f_v(a))` of §3.1 (Agrawal et al., STOC 2027 submission,
manuscript sha256 17239d0b…, p.12 (pdf p.14)): the seed `a` sends the source vertex `v` to the
target vertex `(dom v, f v a)`. -/
def phi {V A B : Type*} {k : ℕ} (dom : V → Fin k) (f : V → A → B) (a : A) (v : V) : Fin k × B :=
  (dom v, f v a)

/-- The image `W_a = ϕ_a(V(G))` of the source vertex set under the seed `a` (§3.1, p.12). -/
def W {V A B : Type*} [Fintype V] [DecidableEq B] {k : ℕ} (dom : V → Fin k) (f : V → A → B)
    (a : A) : Finset (Fin k × B) :=
  Finset.univ.image (phi dom f a)

/-- **The target graph `Z`** (Agrawal et al., STOC 2027 submission, manuscript sha256 17239d0b…,
§3.1, pp.12–13 (pdf pp.14–15)).

Given a source graph `G` with domains `dom : V → Fin k` and a family of maps
`F = {f_v : A → B}_{v ∈ V(G)}`, the target graph has vertex set `[k] × B` and edge set
`E(Z) = ⋃_{a ∈ A} {{ϕ_a(u), ϕ_a(v)} : (u, v) ∈ E(G)}`: two target vertices are adjacent when some
seed `a` maps an edge of `G` onto them.

**Formalization Note.** Domains are `Fin k` (`0, …, k-1`). The clause `x ≠ y` keeps `Z` loopless
for every family; when every `ϕ_a` is injective (copy injectivity, §3.1, p.13) it is implied, so
`Z` is exactly the paper's graph. The family is a function `f : V → A → B`, `f v = f_v`. -/
def target {V A B : Type*} {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k) (f : V → A → B) :
    SimpleGraph (Fin k × B) where
  Adj x y := x ≠ y ∧ ∃ a u v, G.Adj u v ∧ phi dom f a u = x ∧ phi dom f a v = y
  symm := ⟨by
    rintro x y ⟨hxy, a, u, v, huv, rfl, rfl⟩
    exact ⟨fun h => hxy h.symm, a, v, u, huv.symm, rfl, rfl⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end HiddenPartition


