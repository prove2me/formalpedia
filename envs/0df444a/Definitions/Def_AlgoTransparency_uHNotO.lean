-- Prove2me | Definitions.Def_AlgoTransparency_uHNotO
-- name    : AlgoTransparency_uHNotO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:28.433626+00:00
-- url     : https://prove2.me/theorems/36724fd1-3ffc-44eb-818c-040641213b2c
-- title:
--   Opaque utility of an H agent who does not improve education
-- statement:
--   In the opaque game a type-H agent who does not improve education gets
--
--   $$
--   u^H_{\mathrm{not}}=\lambda P_AR+(1-\lambda)P_CR .
--   $$
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (5), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_OState

namespace AlgoTransparency

/-- **Utility of a type-H agent who does not improve education, opaque game**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, eq. (5), p.14 (PDF 15):

`λ P_A R + (1 − λ) P_C R`,

where `P` is the firm's vector of hiring probabilities over the states `A, B, C, D`.

**Formalization Note.** This is the utility of one agent; the paper's per-type totals
`Π^H = θ u^H`, `Π^L = (1 − θ) u^L` (App. A.1) order equilibria the same way. -/
def uHNotO (p : Params) (P : OState → ℝ) : ℝ :=
  p.lam * P .A * p.R + (1 - p.lam) * P .C * p.R

end AlgoTransparency


