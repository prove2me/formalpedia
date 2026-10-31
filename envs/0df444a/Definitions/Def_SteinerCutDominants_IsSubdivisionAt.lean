-- Prove2me | Definitions.Def_SteinerCutDominants_IsSubdivisionAt
-- name    : SteinerCutDominants_IsSubdivisionAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:20.002553+00:00
-- url     : https://prove2.me/theorems/7ebad75b-98f5-4c5b-b455-dc858385ad4e
-- title:
--   Subdivision with new node $w$
-- statement:
--   $(G,T)$ is obtained by a **subdivision** from $(G',T')$ with new node $w$ if $G$ arises from $G'$ by replacing an edge $uv$ with the edges $uw$ and $vw$, where $w$ is a newly added node, and $T=T'$; in particular $w\notin T$. The weight vector $c$ of $G$ is the subdivided vector
--   $$
--   c(uw)=c(vw)=c'(uv),\qquad c(e)=c'(e)\ \text{ for all other edges.}
--   $$
--   Read in reverse, this relation is **reducing** the node $w$ (p.9).
--
--   **Formalization Note** $V(G')$ is identified with $V(G)\setminus\{w\}$ by an embedding, so the relation holds up to isomorphism.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §5, p.8

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wt

namespace SteinerCutDominants

/-- `H` is obtained from `H'` by a subdivision with new node `w` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §5, p.8): `G` arises from `G'` by replacing an edge
`uv` with the edges `uw` and `vw`, `T = T'`, and `c(uw) = c(vw) = c'(uv)` and `c(e) = c'(e)` on all
other edges.

**Formalization Note** The embedding `φ` identifies `V(G')` with `V(G) \ {w}`, so that the relation
holds up to isomorphism by construction. Hence `w ∉ T`. Read from right to left, this relation is
also "`H'` arises from `H` by reducing `w`" (p.9). -/
def IsSubdivisionAt (H' H : WSG) (w : H.V) : Prop :=
  ∃ (φ : H'.V ↪ H.V) (u v : H'.V), H'.G.Adj u v ∧
    Set.range φ = {w}ᶜ ∧
    H.T = H'.T.map φ ∧
    (∀ x y, H.G.Adj (φ x) (φ y) ↔ H'.G.Adj x y ∧ s(x, y) ≠ s(u, v)) ∧
    (∀ x, H.G.Adj (φ x) w ↔ x = u ∨ x = v) ∧
    (∀ x y, s(x, y) ≠ s(u, v) → H.wt (φ x) (φ y) = H'.wt x y) ∧
    H.wt (φ u) w = H'.wt u v ∧ H.wt (φ v) w = H'.wt u v

end SteinerCutDominants


