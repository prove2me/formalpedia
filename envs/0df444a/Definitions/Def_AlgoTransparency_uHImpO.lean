-- Prove2me | Definitions.Def_AlgoTransparency_uHImpO
-- name    : AlgoTransparency_uHImpO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:08.252989+00:00
-- url     : https://prove2.me/theorems/85561e08-29e4-4d58-ab3e-6f49656faef4
-- title:
--   Opaque utility of an H agent who improves education
-- statement:
--   In the opaque game a type-H agent who improves education is hired with probability $P_B$ if high on the correlational feature (probability $\lambda$) and $P_D$ otherwise, and pays $C_H$:
--
--   $$
--   u^H_{\mathrm{imp}}=\lambda P_BR+(1-\lambda)P_DR-C_H .
--   $$
--
--   **Formalization Note** This is a single agent's utility; the per-type totals of App. A.1 are $\theta u^H$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (5), p.14 (PDF 15)

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_OState

namespace AlgoTransparency

/-- **Utility of a type-H agent who improves education, opaque game**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, eq. (5), p.14 (PDF 15):

`λ P_B R + (1 − λ) P_D R − C_H`,

where `P` is the firm's vector of hiring probabilities over the states `A, B, C, D`. `CH` is the type-H agent's cost of improving education (the paper's `C_H`).

**Formalization Note.** This is the utility of one agent; the paper's per-type totals
`Π^H = θ u^H`, `Π^L = (1 − θ) u^L` (App. A.1) order equilibria the same way. -/
def uHImpO (p : Params) (CH : ℝ) (P : OState → ℝ) : ℝ :=
  p.lam * P .B * p.R + (1 - p.lam) * P .D * p.R - CH

end AlgoTransparency


