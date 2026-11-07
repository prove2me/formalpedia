-- Prove2me | Definitions.Def_DDNNFNeg_HasEdge
-- name    : DDNNFNeg_HasEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:05.888554+00:00
-- url     : https://prove2.me/theorems/67687f00-9a7d-49b5-8efe-03ea562f76c3
-- title:
--   $G_x$ contains an edge
-- statement:
--   For an assignment $x \in \{0,1\}^{[n]}$, the induced subgraph $G_x$ **contains an edge** if some edge of $G$ has both endpoints in $x$; equivalently, $x$ is not an independent set of $G$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.1, p.11

import Mathlib

namespace DDNNFNeg

/-- `G_x` contains at least one edge (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.1, p.11): some edge of `G` has both endpoints
set to `1` by `x`, i.e. `{i | x i = 1}` is not an independent set of `G`. -/
def HasEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : Prop :=
  ∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    Decidable (HasEdge G x) := by
  unfold HasEdge; infer_instance

end DDNNFNeg


