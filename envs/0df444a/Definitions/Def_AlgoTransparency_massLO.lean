-- Prove2me | Definitions.Def_AlgoTransparency_massLO
-- name    : AlgoTransparency_massLO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:34.637843+00:00
-- url     : https://prove2.me/theorems/ae815e64-b9f0-4f15-b57c-593409f80bf0
-- title:
--   Mass $n^L_S$ of L agents in each opaque state
-- statement:
--   If every type-L agent improves education with probability $q_L\in[0,1]$, the (expected) mass of L agents in each opaque state is
--
--   $$
--   n^L_A=(1-\theta)(1-\lambda)(1-q_L),\quad n^L_B=(1-\theta)(1-\lambda)q_L,\quad n^L_C=(1-\theta)\lambda(1-q_L),\quad n^L_D=(1-\theta)\lambda q_L .
--   $$
--
--   **Formalization Note** Common mixed strategy per type and expected masses, as for $n^H_S$.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3.1 and §4, pp.14, 16–17 (PDF 15, 17–18); App. A.1, pp.41–44

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_OState

namespace AlgoTransparency

/-- **Mass of type-L agents in each opaque state**, `n^L_S`, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §3.1 and §4, pp.14, 16–17 (PDF 15, 17–18), when every L agent improves
education with probability `qL`:

* `n^L_A = (1 − θ)(1 − λ)(1 − qL)`, `n^L_B = (1 − θ)(1 − λ) qL`,
* `n^L_C = (1 − θ)λ(1 − qL)`, `n^L_D = (1 − θ)λ qL`.

**Formalization Note.** As for `massHO`: a common mixed strategy `qL ∈ [0, 1]` per type and
expected masses. A share `1 − λ` of L agents is high on the correlational feature (p.12). -/
def massLO (p : Params) (qL : ℝ) : OState → ℝ
  | .A => (1 - p.θ) * (1 - p.lam) * (1 - qL)
  | .B => (1 - p.θ) * (1 - p.lam) * qL
  | .C => (1 - p.θ) * p.lam * (1 - qL)
  | .D => (1 - p.θ) * p.lam * qL

end AlgoTransparency


