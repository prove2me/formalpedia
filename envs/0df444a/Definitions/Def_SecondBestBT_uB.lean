-- Prove2me | Definitions.Def_SecondBestBT_uB
-- name    : SecondBestBT_uB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:44.116511+00:00
-- url     : https://prove2.me/theorems/3a22828f-713a-410f-b91f-68b3e5a13c88
-- title:
--   Buyer's interim utility $u_B(b,b')$
-- statement:
--   For a mechanism $(x,p_B,p_S)$ and a seller prior $F_S$, the interim expected utility of a buyer with true value $b$ who reports $b'$ is
--   $$
--   u_B(b,b')=\int\big(b\,x(s,b')-p_B(s,b')\big)\,dF_S(s).
--   $$
--   The expectation is over the seller's value.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

open MeasureTheory

namespace SecondBestBT

/-- The buyer's interim expected utility `u_B(b, b') = ∫ (b·x(s, b') − p_B(s, b')) dF_S(s)` of a
buyer with true value `b` who reports `b'` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version
sha256 17184930…, Section 2, p.4).

**Formalization Note** The integral is over the seller prior `μS` on `ℝ`; for a prior supported
on the type set it equals the paper's integral over that set. Integrability of the integrand is
guaranteed by `WellDefined`. -/
noncomputable def uB (μS : Measure ℝ) (M : Mechanism) (b b' : ℝ) : ℝ :=
  ∫ s, (b * M.x (s, b') - M.pB (s, b')) ∂μS

end SecondBestBT


