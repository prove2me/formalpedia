-- Prove2me | Definitions.Def_DotySW_Deranged_eIdem
-- name    : DotySW_Deranged_eIdem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:49.679184+00:00
-- url     : https://prove2.me/theorems/b81cc813-c239-4ff1-bed0-575fc9442e38
-- title:
--   The idempotent $e=\prod_i(1-n^{-1}c_{i,-i})$
-- statement:
--   Let $c_{i,-i}$ be the $(r,r)$-diagram with a horizontal edge connecting $i$ and $-i$ on the top row and on the bottom row, and all other edges vertical. The element
--
--   $$
--   e=\prod_{i=1}^{r}\bigl(1-n^{-1}c_{i,-i}\bigr)\in\mathcal B^{(n)}_{r,r}
--   $$
--
--   is the idempotent attached to the summand $\mathfrak{sl}_n^{\otimes r}$ of $V^{r,r}$.
--
--   **Formalization Note** Position $-i$ is `Fin.natAdd r i`, as $c_{i,-j}$ is the diagram $c_{i,r+j}$ (p. 7). The factors commute, so the order of the product is immaterial. In Lean $0^{-1}=0$, so the element is only meaningful for $n\ne0$, which $n\ge 2r$ gives when $r\ge1$.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, unnumbered (after Eq. (17)), p. 11, in the notation of §3.1, p. 7

import Mathlib
import Definitions.Def_DotySW_Deranged_WB

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The idempotent `e = ∏_i (1 - n⁻¹ c_{i,-i})` of `B^{(n)}_{r,r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, unnumbered (after Eq. (17)), p. 11, in the notation of §3.1, p. 7.

**Formalization Note** The diagram `c_{i,-i}` is `WalledDiagram.E (Fin.castAdd r i) (Fin.natAdd r i)`:
position `-i` is position `r + i` ("`c_{i,-j}` is the `(r + s)`-diagram denoted by `c_{i,r+j}`",
p. 7). The factors commute, so the order of the product is immaterial. In Lean `(0 : ℂ)⁻¹ = 0`, so
`eIdem 0 r = 1`; the paper's `e` needs `n ≠ 0`, and `n ≥ 2r` with `r ≥ 1` gives it. -/
noncomputable def eIdem (n r : ℕ) : WB n r r :=
  ((List.finRange r).map fun i =>
    (1 : WB n r r) - (n : ℂ)⁻¹ • (diag (WalledDiagram.E (Fin.castAdd r i) (Fin.natAdd r i)) : WB n r r)).prod

end DotySW.Deranged


