-- Prove2me | Definitions.Def_DDNNFNeg_IsFree
-- name    : DDNNFNeg_IsFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:05.653767+00:00
-- url     : https://prove2.me/theorems/48a20473-af28-464f-8bc5-7aea6ebb4acd
-- title:
--   Edge free with respect to an assignment
-- statement:
--   An edge $e$ is **free** with respect to an assignment $z$ if $z(t) = 0$ for every $t \in N(e) \setminus e$, i.e. every neighbour of an endpoint of $e$, other than the endpoints themselves, is set to $0$.
--
--   Applied to the random independent set $X$, this predicate is the indicator $Y_i$ of the proof of Lemma 5.6.
--
--   **Formalization Note** The paper takes $z \in \{0,1\}^Z$ with $Z$ the vertices not incident to the chosen edges; here $z$ is a full assignment of which only the values on $N(e) \setminus e$ are read.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, p.13 (free edges) and p.14 ($Y_i$)

import Mathlib
import Definitions.Def_DDNNFNeg_edgeNbhd

namespace DDNNFNeg

/-- The edge `e` is free with respect to the assignment `z` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.2, p.13): `z(t) = 0`
for every vertex `t ∈ N(e) \ e`, i.e. every neighbour of an endpoint of `e`, other than the
endpoints themselves, is set to `0`.

**Formalization Note** The paper takes `z ∈ {0,1}^Z` with `Z` the vertices not incident to the
chosen edges; here `z : Fin n → Bool` is a full assignment, of which only the values on
`N(e) \ e` are read. For the chosen edges (pairwise disjoint neighbourhoods) `N(e) \ e ⊆ Z`.
The same predicate, applied to the random independent set `X`, is the indicator `Y_i` of the
proof of Lemma 5.6 (p.14). -/
def IsFree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : Sym2 (Fin n))
    (z : Fin n → Bool) : Prop :=
  ∀ t ∈ edgeNbhd G e, t ∉ e → z t = false

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : Sym2 (Fin n))
    (z : Fin n → Bool) : Decidable (IsFree G e z) := by
  unfold IsFree; infer_instance

end DDNNFNeg


