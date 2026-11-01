-- Prove2me | Definitions.Def_PacingComplexity_GBuyer
-- name    : PacingComplexity_GBuyer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:24.157384+00:00
-- url     : https://prove2.me/theorems/9454b681-f53c-496a-a980-af3a7a70509a
-- title:
--   Buyers of the gadget game: $C(p,s)$, $D(p,s)$ and $T$
-- statement:
--   The gadget game built from an $n\times n$ bimatrix game has $4n+1$ buyers:
--
--   1. a buyer $C(p,s)$ for each player $p\in\{1,2\}$ and pure strategy $s\in[n]$;
--   2. a dummy buyer $D(p,s)$ for each $p\in\{1,2\}$ and $s\in[n]$;
--   3. one threshold buyer $T$.
--
--   **Formalization Note** $p$ ranges over a two-element index set, with the first element standing for player 1.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, pp.30–31

import Mathlib

namespace PacingComplexity

/-- **Buyers of the gadget game** `G` built from an `n × n` bimatrix game (Chen, Kroer, Kumar, *The
Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, Appendix A, p.31): the buyers
`C(p, s)` and the dummy buyers `D(p, s)` for `p ∈ {1, 2}` and `s ∈ [n]`, and the threshold buyer
`T`; `4n + 1` buyers in all (p.30: "an SPP game G with 4n+1 buyers").

**Formalization Note** The player index `p ∈ {1, 2}` is `Fin 2`, with `0` for player 1 and `1` for
player 2; `s ∈ [n]` is `Fin n`. -/
inductive GBuyer (n : ℕ) where
  /-- Buyer `C(p, s)`. -/
  | C (p : Fin 2) (s : Fin n)
  /-- Dummy buyer `D(p, s)`. -/
  | D (p : Fin 2) (s : Fin n)
  /-- Threshold buyer `T`. -/
  | T
  deriving DecidableEq, Fintype

end PacingComplexity


