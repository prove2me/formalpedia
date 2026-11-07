-- Prove2me | Definitions.Def_HardCoreBochner_avail
-- name    : HardCoreBochner_avail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:10.711788+00:00
-- url     : https://prove2.me/theorems/1767ef37-e14c-48fa-9bae-76e8b6b3b4bb
-- title:
--   Vertices of $G_\sigma$: sites available at an independent set
-- statement:
--   For a graph $G$ and an independent set $\sigma$, $G_\sigma$ is the graph that remains when $\sigma$ and its neighbours are removed from $G$. A vertex $v$ is a vertex of $G_\sigma$ (is **available** at $\sigma$) when $v\notin\sigma$ and no neighbour of $v$ lies in $\sigma$; these are exactly the vertices that can be added to $\sigma$ keeping it independent. $G_\sigma$ is the subgraph of $G$ induced on them.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.1, p.4 (PDF p.4)

import Mathlib

namespace HardCoreBochner

/-- The vertices of `G_σ`, "the graph that remains when we remove σ and its neighbors from G".
Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of Theorem 1.1, p.4. A vertex `v` is **available** at `σ` when `v ∉ σ` and no neighbour
of `v` lies in `σ`.

**Formalization Note** `G_σ` is the subgraph of `G` induced on these vertices, so its adjacency
matrix is the principal submatrix of `A_G` on them. -/
def avail {V : Type*} (G : SimpleGraph V) (σ : V → Bool) (v : V) : Prop :=
  σ v = false ∧ ∀ w, G.Adj v w → σ w = false

instance {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V → Bool) :
    DecidablePred (avail G σ) :=
  fun v => inferInstanceAs (Decidable (σ v = false ∧ ∀ w, G.Adj v w → σ w = false))

end HardCoreBochner


