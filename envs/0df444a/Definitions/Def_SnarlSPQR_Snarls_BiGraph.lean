-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_BiGraph
-- name    : SnarlSPQR_Snarls_BiGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:27:39.995515+00:00
-- url     : https://prove2.me/theorems/ca8eae67-5acf-4fae-87ae-03b8c4f1631f
-- title:
--   Bidirected graphs: signs, vertex-sides, tips, signed neighbourhoods, the underlying undirected multigraph, blocks and maximal 2-connected subgraphs
-- statement:
--   A **sign** is $+$ or $-$. The opposite of $\alpha$ is written $\hat\alpha$. A **vertex-side** $v\alpha$ is a pair of a vertex $v$ and a sign $\alpha$.
--
--   A **bidirected graph** $G=(V,E)$ has a finite set $V$ of vertices and a finite set $E$ of bidirected edges. Each edge is an unordered pair $\{u\alpha,v\beta\}$ of vertex-sides; it is incident to $u$ with sign $\alpha$ and to $v$ with sign $\beta$. Because $E$ is a set, $G$ has no parallel edges in the paper's sense (§3), but $\{u+,v-\}$ and $\{u+,v+\}$ are different edges. A **valid** graph is loopless (§5.1): no edge has both vertex-sides at the same vertex, and every vertex of an edge lies in $V$.
--
--   - The **vertex-sides of $G$** are the elements of its edges.
--   - $G$ has a vertex-side of sign $\alpha$ in $v$ if some edge contains $v\alpha$.
--   - $v$ is a **tip** of $G$ if no two edges of $G$ are incident to $v$ with different signs.
--   - $N^\alpha_G(v)$ is the set of vertices $x$ with an edge $\{v\alpha,x\beta\}$.
--   - The **underlying undirected graph** $U(G)$ forgets the signs and keeps every edge, so its edges keep their identities and it may have parallel edges.
--   - Connectivity words applied to $G$ (block, 2-connected, maximal 2-connected subgraph, separation pair) mean those of $U(G)$ (p. 9).
--   - A **subgraph** $H\subseteq G$ has $V(H)\subseteq V(G)$ and $E(H)\subseteq E(G)$.
--   - The subgraph **induced** by a vertex set $S$ has the edges with both ends in $S$. The subgraph induced by an edge set $F$ has the edges $F$ and their endpoints; the expansions of an SPQR tree are of this kind.
--
--   **Formalization Note.** `BiGraph V` has `verts : Finset V` and `edges : Finset (Sym2 (V × Sign))`, and `Valid` is a predicate. `U G : MGraph V (Sym2 (V × Sign))` uses the bidirected edges themselves as edge identities, with endpoint map `Sym2.map Prod.fst`. `AllSidesAt G v α` says that every vertex-side of $G$ at $v$ has sign $\alpha$ ("$v$ is a tip with sign $\alpha$").
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 5, §2.2; p. 9 (remark on notation, no parallel edges); p. 28, §5.1 (no loops)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_Multigraph

open Classical

namespace SnarlSPQR.Snarls

/-!
# Bidirected graphs, vertex-sides, tips, and the underlying undirected multigraph (§2.2, p. 5)

Sena et al., arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), §2.2 (p. 5), the remark on
notation (p. 9), the no-parallel-edges assumption of §3 (p. 9) and the no-loops assumption of
§5.1 (p. 28).

* A **sign** is `+` or `−`; the opposite sign of `α` is `α̂` (`Sign.opp`).
* A **vertex-side** `vα` is a pair `(v, α) : V × Sign`.
* A **bidirected graph** `G` has a finite vertex set `G.verts` and a finite set `G.edges` of
  bidirected edges, each an unordered pair `{uα, vβ}` of vertex-sides (`Sym2 (V × Sign)`). The
  edges form a `Finset`, so there are no parallel edges in the sense of §3 (`{xα, yβ}` and
  `{zγ, wδ}` with `x = z, α = γ, y = w, β = δ`); `{u+, v−}` and `{u+, v+}` are distinct edges.
  `G.Valid` says every vertex of an edge is a vertex of `G` and `G` has no loops (`u ≠ v` in every
  edge `{uα, vβ}`), the standing assumption of §5.
* The **vertex-sides of `G`** are the elements of its edges (`G.sides`); `G` has a vertex-side of
  sign `α` in `v` (`G.HasSide v α`) if some edge contains `vα`.
* `v` is a **tip** of `G` if no two edges of `G` are incident to `v` with different signs.
* `N^α_G(v)` (`G.nbr α v`) is the set of vertices `x` with an edge `{vα, xβ}`.
* `U(G)` (`G.U`) is the undirected multigraph obtained by forgetting signs; the edge identities
  are the bidirected edges themselves, so parallel edges of `U(G)` are kept.
* Connectivity words applied to a bidirected graph mean those of `U(G)` (p. 9): blocks
  (`IsBlock`), maximal 2-connected subgraphs (`IsMax2Conn`).
* A bidirected **subgraph** `H` of `G` has `V(H) ⊆ V(G)` and `E(H) ⊆ E(G)`; subgraphs of `G` and
  subgraphs of `U(G)` correspond through `U`.
-/

/-- A sign: `+` (`pos`) or `−` (`neg`). -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq

/-- The opposite sign `α̂`. -/
def Sign.opp : Sign → Sign
  | .pos => .neg
  | .neg => .pos

/-- A bidirected graph: a finite set of vertices and a finite set of bidirected edges (unordered
pairs of vertex-sides). -/
structure BiGraph (V : Type*) where
  verts : Finset V
  edges : Finset (Sym2 (V × Sign))

namespace BiGraph

variable {V : Type*}

/-- `G` is a loopless bidirected graph: every vertex of an edge is a vertex of `G`, and no edge
has both vertex-sides at the same vertex. -/
def Valid (G : BiGraph V) : Prop :=
  (∀ e ∈ G.edges, ∀ p ∈ e, p.1 ∈ G.verts) ∧ ∀ e ∈ G.edges, ¬ (e.map Prod.fst).IsDiag

/-- `H` is a subgraph of `G`. -/
def IsSubgraph (H G : BiGraph V) : Prop := H.verts ⊆ G.verts ∧ H.edges ⊆ G.edges

/-- The set of vertex-sides of `G`: the union of its edges. -/
noncomputable def sides (G : BiGraph V) : Finset (V × Sign) := G.edges.biUnion fun e => e.toFinset

/-- `G` has a vertex-side of sign `α` in `v`: some edge of `G` contains `vα`. -/
def HasSide (G : BiGraph V) (v : V) (α : Sign) : Prop := ∃ e ∈ G.edges, (v, α) ∈ e

/-- `v` is a tip of `G`: no two edges of `G` are incident to `v` with different signs. -/
def IsTip (G : BiGraph V) (v : V) : Prop := ¬ (G.HasSide v .pos ∧ G.HasSide v .neg)

/-- All vertex-sides of `G` at `v` have sign `α` (`v` is a tip with sign `α`). -/
def AllSidesAt (G : BiGraph V) (v : V) (α : Sign) : Prop := ∀ σ, G.HasSide v σ → σ = α

/-- `N^α_G(v)`: the vertices `x` with an edge `{vα, xβ}` in `G`. -/
def nbr (G : BiGraph V) (α : Sign) (v : V) : Set V := {x | ∃ β, s((v, α), (x, β)) ∈ G.edges}

/-- The underlying undirected multigraph `U(G)`: forget the signs, keep every edge. -/
def U (G : BiGraph V) : MGraph V (Sym2 (V × Sign)) where
  verts := G.verts
  edges := G.edges
  ends := Sym2.map Prod.fst

/-- The vertex-induced subgraph `G[S]`. -/
noncomputable def induce (G : BiGraph V) (S : Finset V) : BiGraph V where
  verts := S
  edges := G.edges.filter fun e => ∀ p ∈ e, p.1 ∈ S

/-- The subgraph induced by a set `F` of bidirected edges: edges `F`, vertices their endpoints.
The expansion of an SPQR-tree edge is `edgeInduced` of its real edges. -/
noncomputable def edgeInduced (F : Finset (Sym2 (V × Sign))) : BiGraph V where
  verts := F.biUnion fun e => (e.map Prod.fst).toFinset
  edges := F

/-- `B` is a block of `G`: `U(B)` is a block of `U(G)`. -/
def IsBlock (G B : BiGraph V) : Prop := G.U.IsBlock B.U

/-- `H` is a maximal 2-connected subgraph of `G`. -/
def IsMax2Conn (G H : BiGraph V) : Prop :=
  MGraph.IsMaximalWith (fun C => MGraph.IsSub C G.U ∧ C.TwoConnected) H.U

/-- `H` is a 2-connected subgraph of `G`. -/
def Is2ConnSub (G H : BiGraph V) : Prop := MGraph.IsSub H.U G.U ∧ H.U.TwoConnected

end BiGraph

end SnarlSPQR.Snarls


