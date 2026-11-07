-- Prove2me | Definitions.Def_BrouwerLaplacian_IsSplitWith
-- name    : BrouwerLaplacian_IsSplitWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:21.363199+00:00
-- url     : https://prove2.me/theorems/e6014b45-b1b7-4760-9294-f5f039480bd9
-- title:
--   Split graph with clique $K$ and independent set $S=[n]\setminus K$
-- statement:
--   Let $H$ be a simple graph on a finite vertex set and $K$ a set of vertices. $H$ is **split with clique $K$** if
--
--   1. every two distinct vertices of $K$ are adjacent (the induced subgraph on $K$ is a clique), and
--   2. no two vertices of $S=K^{\mathrm c}$ are adjacent (the induced subgraph on $S$ is an independent set).
--
--   Edges between $K$ and $S$ are arbitrary. A graph is a **split graph** if it is split with clique $K$ for some $K$. Lemma 3.2 bounds the nuclear norm of the centered Laplacian of such a graph in terms of $|K|$ and $|S|$, which is why the clique is named here.
--
--   **Formalization Note** $K=\varnothing$ and $K$ equal to the whole vertex set are allowed, as in the source's definition.
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Definition 2.1, p.2

import Mathlib

namespace BrouwerLaplacian

/-- **Split graph with clique `K` and independent set `S = [n] ∖ K`.**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Definition 2.1, p.2:
"A graph G on vertex set [n] is a split graph if there is a subset K ⊆ [n] such that the
induced subgraph on K is a clique and the induced subgraph on S = [n] \ K is an independent
set."

`IsSplitWith H K` says that `K` is a clique of `H` and its complement `Kᶜ` is an independent set
of `H`. Edges between `K` and `Kᶜ` are unrestricted.

**Formalization Note.** The clique `K` is named (Lemma 3.2 uses `|K|` and `|S|`), rather than
existentially quantified; `H` is a split graph in the sense of Definition 2.1 iff
`IsSplitWith H K` for some `K`. `K = ∅` and `K = [n]` are allowed, as in the definition. -/
def IsSplitWith {V : Type*} (H : SimpleGraph V) (K : Finset V) : Prop :=
  H.IsClique (K : Set V) ∧ H.IsIndepSet (K : Set V)ᶜ

end BrouwerLaplacian


