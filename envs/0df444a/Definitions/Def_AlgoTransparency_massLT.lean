-- Prove2me | Definitions.Def_AlgoTransparency_massLT
-- name    : AlgoTransparency_massLT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:17.667993+00:00
-- url     : https://prove2.me/theorems/9dcbedb5-d58b-4949-9a17-4f3944f5bfad
-- title:
--   Mass of L agents in each transparent state
-- statement:
--   If every type-L agent improves education with probability $q_L$, the (expected) masses of L agents in the transparent states are $n^L_E=(1-\theta)(1-q_L)$ and $n^L_F=(1-\theta)q_L$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3.1 and §4.2, pp.13–14, 19 (PDF 14–15, 20); App. A.2, pp.46–49

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_TState

namespace AlgoTransparency

/-- **Mass of type-L agents in each transparent state**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §3.1 and §4.2, pp.13–14, 19 (PDF 14–15, 20), when every L agent improves
education with probability `qL`: `n^L_E = (1 − θ)(1 − qL)`, `n^L_F = (1 − θ) qL`.

**Formalization Note.** Common mixed strategy per type and expected masses, as in the opaque
game (`massLO`). -/
def massLT (p : Params) (qL : ℝ) : TState → ℝ
  | .E => (1 - p.θ) * (1 - qL)
  | .F => (1 - p.θ) * qL

end AlgoTransparency


