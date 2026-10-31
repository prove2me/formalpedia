-- Prove2me | Definitions.Def_AlgoTransparency_uNotT
-- name    : AlgoTransparency_uNotT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:50.169621+00:00
-- url     : https://prove2.me/theorems/3ee9b02d-a480-479f-93e8-45b6d23c3161
-- title:
--   Transparent utility of an agent who does not improve education
-- statement:
--   In the transparent game an agent of either type who does not improve education gets
--
--   $$
--   u_{\mathrm{not}}=P_ER .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eqs. (7)–(8), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_TState

namespace AlgoTransparency

/-- **Utility of an agent who does not improve education, transparent game**, Wang, Huang,
Jasin & Singh, arXiv:2008.09283v1, eqs. (7)–(8), p.14 (PDF 15): `P_E R`, the same for both
types. -/
def uNotT (p : Params) (P : TState → ℝ) : ℝ :=
  P .E * p.R

end AlgoTransparency


