-- Prove2me | Definitions.Def_PacingComplexity_GGood
-- name    : PacingComplexity_GGood
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:22.708879+00:00
-- url     : https://prove2.me/theorems/72bfcd28-2e3d-4f1d-a43f-c7e3d2590b20
-- title:
--   Goods of the gadget game: $N(p,s)_i$, $E(p,s)_i$ and $T(p,s)$
-- statement:
--   The gadget game built from an $n\times n$ bimatrix game has $4n^2+2n$ goods:
--
--   1. normalization goods $N(p,s)_1,\dots,N(p,s)_n$ for each $p\in\{1,2\}$ and $s\in[n]$;
--   2. expenditure goods $E(p,s)_1,\dots,E(p,s)_n$ for each $p\in\{1,2\}$ and $s\in[n]$;
--   3. a threshold good $T(p,s)$ for each $p\in\{1,2\}$ and $s\in[n]$.
--
--   **Formalization Note** $p$ ranges over a two-element index set, with the first element standing for player 1.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.30

import Mathlib

namespace PacingComplexity

/-- **Goods of the gadget game** `G` built from an `n × n` bimatrix game (Chen, Kroer, Kumar, *The
Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, Appendix A, p.30):
"• Normalization goods: n goods {N(p, s)1, . . . , N(p, s)n} for each p ∈ {1, 2} and s ∈ [n].
• Expenditure goods: n goods {E(p, s)1, . . . , E(p, s)n} for each p ∈ {1, 2} and s ∈ [n].
• Threshold goods T(p, s) for each p ∈ {1, 2} and s ∈ [n]."
That is `4n² + 2n` goods.

**Formalization Note** `N p s i` is `N(p, s)_i`, `E p s i` is `E(p, s)_i` and `Th p s` is the
threshold good `T(p, s)`. The player index `p ∈ {1, 2}` is `Fin 2` (`0` for player 1, `1` for
player 2); `s, i ∈ [n]` are `Fin n`. -/
inductive GGood (n : ℕ) where
  /-- Normalization good `N(p, s)_i`. -/
  | N (p : Fin 2) (s i : Fin n)
  /-- Expenditure good `E(p, s)_i`. -/
  | E (p : Fin 2) (s i : Fin n)
  /-- Threshold good `T(p, s)`. -/
  | Th (p : Fin 2) (s : Fin n)
  deriving DecidableEq, Fintype

end PacingComplexity


