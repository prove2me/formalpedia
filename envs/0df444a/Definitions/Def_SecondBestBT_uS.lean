-- Prove2me | Definitions.Def_SecondBestBT_uS
-- name    : SecondBestBT_uS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:44.012714+00:00
-- url     : https://prove2.me/theorems/5277e38f-d170-4266-91fc-d2af6217ace1
-- title:
--   Seller's interim utility $u_S(s,s')$
-- statement:
--   For a mechanism $(x,p_B,p_S)$ and a buyer prior $F_B$, the interim expected utility of a seller with true value $s$ who reports $s'$ is
--   $$
--   u_S(s,s')=\int\big(p_S(s',b)-s\,x(s',b)\big)\,dF_B(b).
--   $$
--   The seller's utility is measured net of keeping the good: revenue minus the value of the good given away.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

open MeasureTheory

namespace SecondBestBT

/-- The seller's interim expected utility `u_S(s, s') = ∫ (p_S(s', b) − s·x(s', b)) dF_B(b)` of a
seller with true value `s` who reports `s'` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version
sha256 17184930…, Section 2, p.4).

**Formalization Note** As in the paper, the seller's utility is net of keeping the good: it is
revenue minus the value of the good given away, with no `+ s` term. The integral is over the
buyer prior `μB` on `ℝ`. -/
noncomputable def uS (μB : Measure ℝ) (M : Mechanism) (s s' : ℝ) : ℝ :=
  ∫ b, (M.pS (s', b) - s * M.x (s', b)) ∂μB

end SecondBestBT


