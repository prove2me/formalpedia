-- Prove2me | Definitions.Def_AlgoTransparency_uLImpO
-- name    : AlgoTransparency_uLImpO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:02.777995+00:00
-- url     : https://prove2.me/theorems/54bd10b2-ea28-4d12-a317-fe13ff370240
-- title:
--   Opaque utility of an L agent who improves education
-- statement:
--   In the opaque game a type-L agent who improves education is high on the correlational feature with probability $1-\lambda$ and pays $C_L$:
--
--   $$
--   u^L_{\mathrm{imp}}=(1-\lambda)P_BR+\lambda P_DR-C_L .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (6), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_OState

namespace AlgoTransparency

/-- **Utility of a type-L agent who improves education, opaque game**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, eq. (6), p.14 (PDF 15):

`(1 − λ) P_B R + λ P_D R − C_L`,

where `P` is the firm's vector of hiring probabilities over the states `A, B, C, D`. `CL` is the type-L agent's cost of improving education (the paper's `C_L`).

**Formalization Note.** This is the utility of one agent; the paper's per-type totals
`Π^H = θ u^H`, `Π^L = (1 − θ) u^L` (App. A.1) order equilibria the same way. -/
def uLImpO (p : Params) (CL : ℝ) (P : OState → ℝ) : ℝ :=
  (1 - p.lam) * P .B * p.R + p.lam * P .D * p.R - CL

end AlgoTransparency


