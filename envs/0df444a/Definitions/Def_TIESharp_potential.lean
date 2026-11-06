-- Prove2me | Definitions.Def_TIESharp_potential
-- name    : TIESharp_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:12.591789+00:00
-- url     : https://prove2.me/theorems/eec4adc6-a13e-40a8-bb9b-eae74ebb869c
-- title:
--   Cost potential $V^m_i(t)=t_i\cdot q^m_i(t)-\bar p^m_i(t)$
-- statement:
--   Machine $i$'s **cost potential** is its expected processing cost at truthful bids minus its normalized expected payment,
--   $$V^m_i(t)=t_i\cdot q^m_i(t)-\bar p^m_i(t)=\sum_j t_{ij}q^m_{ij}(t)-\bar p^m_i(t),$$
--   the negative of its normalized truthful expected utility. Truthfulness makes it a concave function of the own row (Rochet's representation), and its weak derivatives are the assignment probabilities.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4, p.13

import Mathlib
import Definitions.Def_TIESharp_marg
import Definitions.Def_TIESharp_pbar

set_option autoImplicit false

namespace TIESharp

/-- The **cost potential** (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, §4, p.13): `V^m_i(t) = t_i · q^m_i(t) − p̄^m_i(t)`, machine `i`'s expected
processing cost at truthful bids minus its normalized expected payment, i.e. the negative of its
normalized truthful expected utility. -/
def potential {n : ℕ} (F : Family n) (m : ℕ) (t : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ j, t i j * marg F m t i j - pbar F m t i

end TIESharp


