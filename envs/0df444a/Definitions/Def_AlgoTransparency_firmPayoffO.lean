-- Prove2me | Definitions.Def_AlgoTransparency_firmPayoffO
-- name    : AlgoTransparency_firmPayoffO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:52:30.86329+00:00
-- url     : https://prove2.me/theorems/7ea937cc-060a-4911-a635-e84ed822e7dd
-- title:
--   Firm's payoff $\Pi_O$ in the opaque game
-- statement:
--   For agents' strategies $q_H,q_L$ and hiring probabilities $P=(P_A,P_B,P_C,P_D)$, the firm's total payoff in the opaque game is
--
--   $$
--   \Pi_O=\sum_{S\in\{A,B,C,D\}}P_S\big(n^H_S(W^H_S-R)+n^L_S(W^L_S-R)\big)=\sum_S P_S\,m_S .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (4), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_marginO

namespace AlgoTransparency

/-- **The firm's total payoff in the opaque game**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, eq. (4), p.14 (PDF 15):

`Π_O = Σ_{S ∈ {A,B,C,D}} P_S · (n^H_S (W^H_S − R) + n^L_S (W^L_S − R))`,

for agents' strategies `qH, qL` and hiring probabilities `P`. -/
def firmPayoffO (p : Params) (qH qL : ℝ) (P : OState → ℝ) : ℝ :=
  P .A * marginO p qH qL .A + P .B * marginO p qH qL .B +
    P .C * marginO p qH qL .C + P .D * marginO p qH qL .D

end AlgoTransparency


