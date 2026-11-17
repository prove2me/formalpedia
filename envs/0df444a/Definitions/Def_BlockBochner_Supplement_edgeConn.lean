-- Prove2me | Definitions.Def_BlockBochner_Supplement_edgeConn
-- name    : BlockBochner_Supplement_edgeConn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:31:47.721195+00:00
-- url     : https://prove2.me/theorems/c2b53ed8-845a-4a69-956f-0dc7b1589890
-- title:
--   Connectivity in the spanning subgraph $(V_G,F)$ of a multigraph
-- statement:
--   Let $G$ be a finite multigraph with vertex set $W$ and edge set $E$, where each edge $e$ has an unordered pair of endpoints (equal for a loop). For an edge subset $F\subseteq E$ and vertices $u,v$, $u$ and $v$ are connected in $(W,F)$ when they are joined by a walk using only edges of $F$ (every vertex is connected to itself).
--
--   It is used to define forests and the event that two edges lie in the same tree component of a forest.
--
--   **Formalization Note** The reflexive–transitive closure of "some edge of $F$ has endpoints $\{a,b\}$"; edges are a type with an endpoint map into `Sym2 W`, so parallel edges and loops are allowed.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 5.3, p.33 (PDF p.34)

import Mathlib

namespace BlockBochner.Supplement

/-- **Connectivity in the spanning subgraph `(V_G, F)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 5.3, p.33
(tree components of a forest `F`). For a finite multigraph whose edges `e ∈ α` have endpoints
`ends e ∈ Sym2 W` (a loop has `ends e = s(u, u)`), `edgeConn ends F u v` says that `u` and `v` are
joined by a walk using only edges of `F`.

**Formalization Note** The reflexive–transitive closure of the relation "some edge of `F` has
endpoints `{a, b}`" (symmetric, since `s(a, b) = s(b, a)`). Parallel edges and loops are allowed. -/
def edgeConn {W α : Type*} (ends : α → Sym2 W) (F : Finset α) : W → W → Prop :=
  Relation.ReflTransGen fun a b => ∃ f ∈ F, ends f = s(a, b)

end BlockBochner.Supplement


