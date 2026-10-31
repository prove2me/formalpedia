-- Prove2me | Definitions.Def_AlgoTransparency_massHT
-- name    : AlgoTransparency_massHT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:19.200448+00:00
-- url     : https://prove2.me/theorems/2eda1de2-e4d7-4ce6-9521-b36f4ca109b2
-- title:
--   Mass of H agents in each transparent state
-- statement:
--   If every type-H agent improves education with probability $q_H$, the (expected) masses of H agents in the transparent states are $n^H_E=\theta(1-q_H)$ and $n^H_F=\theta q_H$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3.1 and §4.2, pp.13–14, 19 (PDF 14–15, 20); App. A.2, pp.46–49

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_TState

namespace AlgoTransparency

/-- **Mass of type-H agents in each transparent state**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §3.1 and §4.2, pp.13–14, 19 (PDF 14–15, 20), when every H agent improves
education with probability `qH`: `n^H_E = θ(1 − qH)`, `n^H_F = θ qH`.

**Formalization Note.** Common mixed strategy per type and expected masses, as in the opaque
game (`massHO`). -/
def massHT (p : Params) (qH : ℝ) : TState → ℝ
  | .E => p.θ * (1 - qH)
  | .F => p.θ * qH

end AlgoTransparency


