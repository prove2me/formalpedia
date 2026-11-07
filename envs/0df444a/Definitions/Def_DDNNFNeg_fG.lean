-- Prove2me | Definitions.Def_DDNNFNeg_fG
-- name    : DDNNFNeg_fG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:51.197301+00:00
-- url     : https://prove2.me/theorems/14efb85e-1679-4141-ba63-686ee61124a8
-- title:
--   The function $f_G$: $G_x$ has at least one edge and at most two colours
-- statement:
--   Let $G$ be a graph on $[n]$ with an edge colouring $c$ by the colours $\{1, 2, 3\}$. The Boolean function $f_G : \{0,1\}^{[n]} \to \{0,1\}$ is defined by
--   $$
--   f_G(x) = 1 \iff G_x \text{ contains at least one edge and at most two colours,}
--   $$
--   where $G_x$ is the subgraph of $G$ induced by $\{i : x(i) = 1\}$. Thus $\neg f_G(x) = 1$ if and only if $x$ is an independent set of $G$ or $G_x$ contains all three colours.
--
--   This is the function that separates d-DNNF size from the DNNF size of its negation.
--
--   **Formalization Note** The paper takes $G$ 3-regular with a proper colouring; the definition makes sense for every $G$ and $c$, and the theorems assume those properties where the paper does.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.1, p.11

import Mathlib
import Definitions.Def_DDNNFNeg_HasColor
import Definitions.Def_DDNNFNeg_HasEdge

namespace DDNNFNeg

/-- The Boolean function `f_G : {0,1}^{[n]} → {0,1}` of a graph `G` on `[n]` with an edge
colouring `c` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.1, p.11): `f_G(x) = 1` if and only if the induced subgraph `G_x`
contains at least one edge and at most two colours. Thus `¬f_G(x) = 1` iff `x` is an
independent set of `G` or `G_x` contains all three colours.

**Formalization Note** Vertices are `Fin n`, an assignment is `x : Fin n → Bool` (vertex `i`
is in the set iff `x i = true`), and colours are `Fin 3`. The paper fixes `G` 3-regular with a
proper colouring; the definition makes sense for every `G` and `c`, and the theorems state
those hypotheses where they use them. -/
def fG {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Sym2 (Fin n) → Fin 3)
    (x : Fin n → Bool) : Bool :=
  decide (HasEdge G x ∧ (Finset.univ.filter (fun col : Fin 3 => HasColor G c x col)).card ≤ 2)

end DDNNFNeg


