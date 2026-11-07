-- Prove2me | Definitions.Def_MinBisectFPT_countPoly
-- name    : MinBisectFPT_countPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:14.591204+00:00
-- url     : https://prove2.me/theorems/f07baa40-c03f-45f2-902f-c5c9aa442867
-- title:
--   The polynomial $\sum C_G(\ell,j)y^\ell z^j$
-- statement:
--   For a graph $G$ and $k$, the polynomial
--   $$\sum_{\ell=0}^{|V(G)|}\sum_{j=0}^{k}C_G(\ell,j)\,y^\ell z^j$$
--   with natural coefficients. The proof of Theorem 1.1 multiplies these polynomials over the components of a disconnected graph.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Proof of Theorem 1.1, p.15

import Mathlib
import Definitions.Def_MinBisectFPT_countSets

open scoped Classical

namespace MinBisectFPT

open MvPolynomial in
/-- The polynomial `Σ_{ℓ,j} C_G(ℓ, j) y^ℓ z^j`, `0 ≤ ℓ ≤ |V(G)|`, `0 ≤ j ≤ k`, with `y = X 0` and
`z = X 1`. Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC 2027 submission (manuscript sha256 8db80a52…), Proof of Theorem 1.1, p.15. -/
noncomputable def countPoly {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    MvPolynomial (Fin 2) ℕ :=
  ∑ l ∈ Finset.range (Fintype.card V + 1), ∑ j ∈ Finset.range (k + 1),
    C (countSets G l j) * X 0 ^ l * X 1 ^ j

end MinBisectFPT


