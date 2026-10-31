-- Prove2me | Definitions.Def_FASTournament_ContainsSubgraph
-- name    : FASTournament_ContainsSubgraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:26.537209+00:00
-- url     : https://prove2.me/theorems/4e73a240-9c20-48e1-911e-f867ae70714d
-- title:
--   $G$ contains $H$ as a subgraph
-- statement:
--   A digraph $G$ **contains** a digraph $H$ **as a subgraph** if there is an injective map $f$ from the vertices of $H$ to those of $G$ such that $f(a)f(b)$ is an arc of $G$ whenever $ab$ is an arc of $H$.
--
--   The subgraph need not be induced: $G$ may have further arcs among the vertices $f(a)$. This is the containment used in the definition of Möbius-free tournaments; a Möbius ladder is never an induced subgraph of a tournament.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3

import Mathlib

namespace FASTournament

/-- **`G` contains `H` as a subgraph.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3 ("contains none of K3,3, K′3,3, M5, and M∗5 … as a subgraph").

There is an injective map `f` from the vertices of `H` to those of `G` sending every arc
`a → b` of `H` to an arc `f a → f b` of `G`.

**Formalization Note.** The subgraph need not be induced: `G` may have further arcs among the
image vertices. (No tournament contains a Möbius ladder as an induced subgraph, since the
ladders are not tournaments.) -/
def ContainsSubgraph {W V : Type*} (H : Digraph W) (G : Digraph V) : Prop :=
  ∃ f : W ↪ V, ∀ a b, H.Adj a b → G.Adj (f a) (f b)

end FASTournament


