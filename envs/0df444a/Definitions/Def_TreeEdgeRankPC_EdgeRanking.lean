-- Prove2me | Definitions.Def_TreeEdgeRankPC_EdgeRanking
-- name    : TreeEdgeRankPC_EdgeRanking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:27.742562+00:00
-- url     : https://prove2.me/theorems/7d263063-3a6f-4e72-ba44-c533b449f0fe
-- title:
--   Edge ranking of a tree and the edge ranking number $\mathrm{er}(T)$
-- statement:
--   An **edge ranking** of a tree $T=(V,E)$ is a map $\rho:E\to\mathbb Z_{>0}$ such that the path between any two distinct edges $e,f$ with $\rho(e)=\rho(f)$ contains an edge $g$ with $\rho(g)>\rho(e)$. The **edge ranking number** $\mathrm{er}(T)$ is the least possible maximum rank of an edge ranking of $T$.
--
--   For instance, a path with two edges has $\mathrm{er}=2$, a star with three edges has $\mathrm{er}=3$, and a one-vertex tree has $\mathrm{er}=0$. This is the object of the decision problem of the mission.
--
--   **Formalization Note** A ranking is a function on `Sym2 V`, and only its values on the edges of $T$ matter. "The path between $e$ and $f$" is a path that starts at an endpoint of $e$, ends at an endpoint of $f$, and contains both $e$ and $f$; in a tree there is exactly one. $\mathrm{er}(T)$ is an infimum over natural numbers of a set that is nonempty for a finite graph, since distinct ranks are valid.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.1, p.10

import Mathlib

namespace TreeEdgeRankPC

/-- A **(valid) edge ranking** of a tree `T`, and with it `er(T)`.

Giliberti–Hajiaghayi–Yun, *Parallel Edge Ranking of Trees*, arXiv:2610.12438 (held version of
2026-11-02, sha256 9e04ca7b…), §3.1, p.10: "A (valid) edge ranking of T is a map ρ : E → Z>0 that
assigns positive integer ranks to edges such that the path between any two distinct edges e, f with
ρ(e) = ρ(f) contains an edge g with ρ(g) > ρ(e)."

**Formalization Note.** `ρ` is a function on `Sym2 V`; only its values on `T.edgeSet` matter. Ranks
on edges are required to be at least `1`. "The path between `e` and `f`" is a path `p` that starts at
an endpoint of `e`, ends at an endpoint of `f`, and contains both `e` and `f` as edges. In a tree
there is exactly one such path. A path that merely contains both edges could extend past them, so
the endpoint conditions are essential. Since `ρ e = ρ f`, a witness `g` with `ρ e < ρ g` is never
`e` or `f`, so it makes no difference that `p` includes `e` and `f`. -/
structure IsEdgeRanking {V : Type*} (T : SimpleGraph V) (ρ : Sym2 V → ℕ) : Prop where
  /-- Ranks are positive integers. -/
  pos : ∀ e ∈ T.edgeSet, 1 ≤ ρ e
  /-- The path between two distinct edges of equal rank contains an edge of larger rank. -/
  sep : ∀ e ∈ T.edgeSet, ∀ f ∈ T.edgeSet, e ≠ f → ρ e = ρ f →
    ∀ (u v : V) (p : T.Walk u v), p.IsPath → u ∈ e → v ∈ f → e ∈ p.edges → f ∈ p.edges →
      ∃ g ∈ p.edges, ρ e < ρ g

/-- **`er(T)`**, the least possible maximum rank of an edge ranking of `T`, §3.1, p.10 (arXiv:2610.12438,
held version of 2026-11-02, sha256 9e04ca7b…): "An optimal edge ranking achieves the least possible
maximum rank, denoted by er(T)."

**Formalization Note.** `er T` is the least `k` such that some valid edge ranking has all ranks at
most `k`. For a finite tree the set is nonempty (assign distinct ranks; proved in the mission's
verification file), so the `sInf ∅ = 0` default is never used. A tree with no edge has `er T = 0`, as
on p.15. -/
noncomputable def er {V : Type*} (T : SimpleGraph V) : ℕ :=
  sInf {k | ∃ ρ : Sym2 V → ℕ, IsEdgeRanking T ρ ∧ ∀ e ∈ T.edgeSet, ρ e ≤ k}

end TreeEdgeRankPC


