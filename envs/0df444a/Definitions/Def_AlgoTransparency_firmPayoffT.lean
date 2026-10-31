-- Prove2me | Definitions.Def_AlgoTransparency_firmPayoffT
-- name    : AlgoTransparency_firmPayoffT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:40.548002+00:00
-- url     : https://prove2.me/theorems/f66c57f6-0075-40b3-a11c-aee02e6b48d9
-- title:
--   Firm's payoff $\Pi_T$ in the transparent game
-- statement:
--   For agents' strategies $q_H,q_L$ and hiring probabilities $(P_E,P_F)$, the firm's total payoff in the transparent game is
--
--   $$
--   \Pi_T=P_E\,m_E+P_F\,m_F .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (4), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_marginT

namespace AlgoTransparency

/-- **The firm's total payoff in the transparent game**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, eq. (4), p.14 (PDF 15): `Π_T = P_E m_E + P_F m_F`, for agents' strategies
`qH, qL` and hiring probabilities `P = (P_E, P_F)`. -/
def firmPayoffT (p : Params) (qH qL : ℝ) (P : TState → ℝ) : ℝ :=
  P .E * marginT p qH qL .E + P .F * marginT p qH qL .F

end AlgoTransparency


