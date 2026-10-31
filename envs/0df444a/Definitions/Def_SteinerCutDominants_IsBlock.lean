-- Prove2me | Definitions.Def_SteinerCutDominants_IsBlock
-- name    : SteinerCutDominants_IsBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:21.344715+00:00
-- url     : https://prove2.me/theorems/85f890ba-f494-4b46-96b3-201e7c697207
-- title:
--   The piece of a Steiner graph on $U\cup\{w\}$
-- statement:
--   For a node $w$ and $U\subseteq V(G)$, the weighted Steiner graph $H_1$ with embedding $\varphi_1$ is the piece $(G[U\cup\{w\}],(T\cap U)\cup\{w\})$ of $(G,T)$, with weights proportional to the restriction of $c$ by a positive factor. With $\gcd c_1=1$, $c_1$ is then the minimum integer form of the restriction.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §5, Theorem 3, p.10

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wt

namespace SteinerCutDominants

/-- `H₁` (with `φ₁`) is the piece `(G[U ∪ {w}], (T ∩ U) ∪ {w})` of `H` with the restriction of `c` up
to the positive factor `r` (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, Theorem 3,
p.10). With `IsFacetInducing H₁`, whose `gcd c₁ = 1`, the weights of `H₁` are the minimum integer
form of the restriction of `c`. -/
def IsBlock (H : WSG) (w : H.V) (U : Set H.V) (H₁ : WSG) (φ₁ : H₁.V ↪ H.V) : Prop :=
  Set.range φ₁ = U ∪ {w} ∧
    (∀ x y, H₁.G.Adj x y ↔ H.G.Adj (φ₁ x) (φ₁ y)) ∧
    ((H₁.T.map φ₁ : Finset H.V) : Set H.V) = ((H.T : Set H.V) ∩ U) ∪ {w} ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x y, (H.wt (φ₁ x) (φ₁ y) : ℝ) = r * (H₁.wt x y : ℝ)

end SteinerCutDominants


