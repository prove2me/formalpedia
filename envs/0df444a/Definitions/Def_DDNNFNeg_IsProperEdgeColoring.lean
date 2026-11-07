-- Prove2me | Definitions.Def_DDNNFNeg_IsProperEdgeColoring
-- name    : DDNNFNeg_IsProperEdgeColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:06.397052+00:00
-- url     : https://prove2.me/theorems/c38a5836-8acd-4529-8278-aa60d5106636
-- title:
--   Proper 3-edge-colouring of a graph on $[n]$
-- statement:
--   For a simple graph $G = (V, E)$ on $V = [n]$, a map $c : E \to \{1, 2, 3\}$ is a **proper 3-edge-colouring** if for every vertex $v$ the edges incident on $v$ have distinct colours; equivalently, any two distinct edges sharing a vertex receive distinct colours.
--
--   **Formalization Note** Colours $1, 2, 3$ are $0, 1, 2 \in \mathrm{Fin}\,3$, vertices are $\mathrm{Fin}\,n$, and $c$ is defined on all unordered pairs of vertices; only its values on the edges of $G$ matter.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.3, p.9; §5.1, p.11

import Mathlib

namespace DDNNFNeg

/-- `c` is a proper 3-edge-colouring of the simple graph `G` on `V = [n]`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.3, p.9 and §5.1, p.11): any two distinct edges of `G` that share a vertex receive
distinct colours, i.e. at every vertex the incident edges are coloured with distinct colours.

**Formalization Note** The colours `{1, 2, 3}` are `Fin 3 = {0, 1, 2}`. The colouring is a
function on all unordered pairs `Sym2 (Fin n)`; only its values on the edges `G.edgeSet`
matter. -/
def IsProperEdgeColoring {n : ℕ} (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Fin 3) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → c e ≠ c e'

end DDNNFNeg


