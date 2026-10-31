-- Prove2me | Definitions.Def_AlgoTransparency_uImpT
-- name    : AlgoTransparency_uImpT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:31.301764+00:00
-- url     : https://prove2.me/theorems/f27b7f77-3628-4599-9eeb-4986f7f675ee
-- title:
--   Transparent utility of an agent who improves education
-- statement:
--   In the transparent game an agent with education cost $C$ (that is, $C_H$ for type H and $C_L$ for type L) who improves education gets
--
--   $$
--   u_{\mathrm{imp}}=P_FR-C .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eqs. (7)–(8), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_TState

namespace AlgoTransparency

/-- **Utility of an agent who improves education, transparent game**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, eqs. (7)–(8), p.14 (PDF 15): `P_F R − C`, where `C` is the agent's
cost of improving education (`C_H` for type H, `C_L` for type L).

**Formalization Note.** One definition serves both types; the type enters only through the cost
argument, as in (7)–(8). -/
def uImpT (p : Params) (C : ℝ) (P : TState → ℝ) : ℝ :=
  P .F * p.R - C

end AlgoTransparency


