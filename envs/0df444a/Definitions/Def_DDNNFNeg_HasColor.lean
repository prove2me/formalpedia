-- Prove2me | Definitions.Def_DDNNFNeg_HasColor
-- name    : DDNNFNeg_HasColor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:04.315169+00:00
-- url     : https://prove2.me/theorems/bf2b65c4-7ecf-45b4-8221-b29791ff823a
-- title:
--   $G_x$ contains colour $c$
-- statement:
--   For an assignment $x \in \{0,1\}^{[n]}$, identified with the set $\{i : x(i) = 1\}$, let $G_x$ be the subgraph of $G$ induced by $x$. $G_x$ **contains the colour** $c$ if it contains an edge of colour $c$, i.e. some edge of $G$ with both endpoints in $x$ has colour $c$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.1, p.11

import Mathlib

namespace DDNNFNeg

/-- `G_x` contains the colour `col` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.1, p.11): the subgraph of `G` induced by the
vertex set `{i | x i = 1}` contains an edge of colour `col`, i.e. some edge of `G` with both
endpoints set to `1` by `x` has colour `col`. -/
def HasColor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Sym2 (Fin n) → Fin 3)
    (x : Fin n → Bool) (col : Fin 3) : Prop :=
  ∃ e ∈ G.edgeFinset, (∀ v ∈ e, x v = true) ∧ c e = col

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Sym2 (Fin n) → Fin 3)
    (x : Fin n → Bool) (col : Fin 3) : Decidable (HasColor G c x col) := by
  unfold HasColor; infer_instance

end DDNNFNeg


