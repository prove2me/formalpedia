-- Prove2me | Definitions.Def_AlgoTransparency_uLNotO
-- name    : AlgoTransparency_uLNotO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:11.831294+00:00
-- url     : https://prove2.me/theorems/d55aa626-3719-40df-829e-bcb9669ee89a
-- title:
--   Opaque utility of an L agent who does not improve education
-- statement:
--   In the opaque game a type-L agent who does not improve education gets
--
--   $$
--   u^L_{\mathrm{not}}=(1-\lambda)P_AR+\lambda P_CR .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (6), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_OState

namespace AlgoTransparency

/-- **Utility of a type-L agent who does not improve education, opaque game**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, eq. (6), p.14 (PDF 15):

`(1 − λ) P_A R + λ P_C R`,

where `P` is the firm's vector of hiring probabilities over the states `A, B, C, D`.

**Formalization Note.** This is the utility of one agent; the paper's per-type totals
`Π^H = θ u^H`, `Π^L = (1 − θ) u^L` (App. A.1) order equilibria the same way. -/
def uLNotO (p : Params) (P : OState → ℝ) : ℝ :=
  (1 - p.lam) * P .A * p.R + p.lam * P .C * p.R

end AlgoTransparency


