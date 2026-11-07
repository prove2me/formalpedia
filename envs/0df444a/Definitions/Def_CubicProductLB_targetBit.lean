-- Prove2me | Definitions.Def_CubicProductLB_targetBit
-- name    : CubicProductLB_targetBit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:12.143531+00:00
-- url     : https://prove2.me/theorems/03b5582f-5118-4d62-939b-7fa38359d8df
-- title:
--   The negative-sign bit $b_N$ of the target
-- statement:
--   The **negative-sign bit** of the target is
--   $$b_N(z) = \mathbf 1\{q \mid |z|\} \in \mathbb F_2, \qquad z \in \{0,1\}^N.$$
--   It equals $1$ exactly where $F_{q,N}$ equals $-1$, so that $F_{q,N}(x(z)) = (-1)^{b_N(z)}$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (264), p.31

import Mathlib
import Definitions.Def_ShallowSym_weight

namespace CubicProductLB

/-- The negative-sign bit of the target, `b_N(z) = 1{q ∣ |z|}` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (264), p.31).

**Formalization Note** The bit is `1` exactly where `F_{q,N}` is `-1`. The weight `|z|` is the
published `ShallowSym.weight` (coordinates `Fin N`, `true` for the bit `1`). -/
def targetBit (q N : ℕ) (z : Fin N → Bool) : ZMod 2 :=
  if q ∣ ShallowSym.weight z then 1 else 0

end CubicProductLB


