-- Prove2me | Definitions.Def_DetDLP_TerminalBTN
-- name    : DetDLP_TerminalBTN
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T09:15:08.658406+00:00
-- url     : https://prove2.me/theorems/83bd1250-a4af-40f5-9f44-e8103871d0d1
-- title:
--   Lookup-Separator Bipartite Network Specification and Terminal Instance Encoding
-- statement:
--   This definition module captures the exact graph-theoretic separator structure of the Stage II counterexample-separation Boolean tensor network $\mathcal{N}_y$.
--
--   Given a finite bipartite multigraph $G$ and parameters $(m, k, S, \Delta_{\mathrm{core}})$, a `LookupSeparatorSpec` specifies disjoint vertex subsets $V_{\mathrm{lookup}}$ (of size $4m$, each of degree $k$) and $V_{\mathrm{subdiv}}$ (of size $\beta = 4mk$, each of degree $2$) such that every edge incident to $V_{\mathrm{lookup}}$ terminates at $V_{\mathrm{subdiv}}$, each subdivision vertex has exactly one edge to $V_{\mathrm{lookup}}$ (and thus one internal core edge, $\tau = 1$), deleting $V_{\mathrm{lookup}}$ leaves at most $S$ core edges, and every vertex outside $V_{\mathrm{lookup}}$ has degree at most $\Delta_{\mathrm{core}}$. It also defines `encodeTerminalBTNInstance`, passing the graph, parameters $(b, m, k, S, P_0, \ell)$, and the $n_V$-bit lookup-vertex indicator explicitly to the contraction machine.
--
--   **Formalization Note** Explicitly passing the lookup-vertex indicator keeps the contraction input self-contained while adding only $n_V \le \mathrm{poly}(S + \mathcal{L})$ bits.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.2(3) and Theorem 4.3 (p. 16)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

/-- Structural specification of a lookup-separator bipartite Boolean tensor network `N_y`
(Section 4.2(3) and Theorem 4.3, p. 16):
* `lookupVerts` is a set of `4m` lookup vertices, each of degree `k`, with total boundary arity
  `β = 4mk`;
* `termSubdivVerts` is a disjoint set of `β = 4mk` distinct degree-2 subdivision vertices
  (each having `τ = 1` terminal leg to a lookup vertex and `1` internal port in the core);
* every edge incident to a lookup vertex has its other endpoint in `termSubdivVerts`;
* removing `lookupVerts` leaves a core with at most `S` internal edges and maximum degree at most
  `Δcore`. -/
structure LookupSeparatorSpec (G : BipartiteMultigraph) (m k S Δcore : ℕ) where
  lookupVerts : Finset (Fin G.nV)
  termSubdivVerts : Finset (Fin G.nV)
  disjoint_verts : Disjoint lookupVerts termSubdivVerts
  card_lookup : lookupVerts.card = 4 * m
  card_termSubdiv : termSubdivVerts.card = 4 * m * k
  lookup_deg : ∀ v ∈ lookupVerts, G.deg v = k
  subdiv_deg : ∀ v ∈ termSubdivVerts, G.deg v = 2
  lookup_edges_to_subdiv : ∀ e : Fin G.nE,
    ((G.endpoints e).1 ∈ lookupVerts → (G.endpoints e).2 ∈ termSubdivVerts) ∧
    ((G.endpoints e).2 ∈ lookupVerts → (G.endpoints e).1 ∈ termSubdivVerts)
  subdiv_one_lookup_edge : ∀ v ∈ termSubdivVerts,
    (Finset.univ.filter fun e : Fin G.nE =>
      ((G.endpoints e).1 = v ∧ (G.endpoints e).2 ∈ lookupVerts) ∨
      ((G.endpoints e).2 = v ∧ (G.endpoints e).1 ∈ lookupVerts)).card = 1
  core_edges_le :
    (Finset.univ.filter fun e : Fin G.nE =>
      (G.endpoints e).1 ∉ lookupVerts ∧ (G.endpoints e).2 ∉ lookupVerts).card ≤ S
  core_deg_le : ∀ v : Fin G.nV, v ∉ lookupVerts → G.deg v ≤ Δcore

/-- Canonical binary input encoding of a terminal-preserving lookup-separator BTN instance:
`(desc, G, b, m, k, S, P₀, ℓ, lookupIndicator)` where `lookupIndicator` is the `nV`-bit
membership indicator of `lookupVerts`. -/
def encodeTerminalBTNInstance (desc : List Bool) (G : BipartiteMultigraph)
    (b m k S P0 ℓ : ℕ) (lookupVerts : Finset (Fin G.nV)) : List Bool :=
  OAI.Algorithms.SubexponentialSAT.Encoding.encodeList id
    [ desc,
      G.encode,
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord b,
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord m,
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord k,
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord S,
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord P0,
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord ℓ,
      List.ofFn (fun v : Fin G.nV => decide (v ∈ lookupVerts)) ]

end DetDLP


