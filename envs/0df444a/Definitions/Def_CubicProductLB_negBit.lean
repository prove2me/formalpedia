-- Prove2me | Definitions.Def_CubicProductLB_negBit
-- name    : CubicProductLB_negBit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:43.301196+00:00
-- url     : https://prove2.me/theorems/8edbe8c5-7bd0-4e9f-88ba-f0119bd253ff
-- title:
--   The negative-sign bit $b_P$ of a factor
-- statement:
--   For a factor $P$, the **negative-sign bit** $b_P : \{0,1\}^n \to \mathbb F_2$ is $0$ where $P(x(z)) = 1$ and $1$ where $P(x(z)) = -1$, so that for a unit $P(x(z)) = (-1)^{b_P(z)}$.
--
--   **Formalization Note** The page defines the bit for unit-valued $P$. On a general listing the value $0$ also gives the bit $0$; on a factor of a representation that value does not occur, since the target is nowhere zero.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Eqs. (340)–(341), pp.38–39

import Mathlib
import Definitions.Def_CubicProductLB_ListedFactor
import Definitions.Def_CubicProductLB_signPt

namespace CubicProductLB

/-- The negative-sign bit `b_P` of a factor: `0` where `P(x(z)) = 1` and `1` where `P(x(z)) = -1`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Eq. (340), p.38).

**Formalization Note** The page defines the bit for unit-valued `P`; here a value `0` also gives the
bit `0`, but on a factor of a representation that value does not occur. -/
def negBit {n : ℕ} (l : ListedFactor n) (z : Fin n → Bool) : ZMod 2 :=
  if ListedFactor.eval l (signPt z) = -1 then 1 else 0

end CubicProductLB


