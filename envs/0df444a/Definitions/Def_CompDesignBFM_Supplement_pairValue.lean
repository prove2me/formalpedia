-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_pairValue
-- name    : CompDesignBFM_Supplement_pairValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:05:47.513949+00:00
-- url     : https://prove2.me/theorems/99605525-3888-4fec-9fa6-043ccc1b825d
-- title:
--   The 2-PH valuation (39)
-- statement:
--   On two agents $N=\{1,2\}$, the valuation (39) is
--
--   $$v(\emptyset)=v(\{1\})=v(\{2\})=0,\qquad v(\{1,2\})=1,$$
--
--   a positive hypergraph valuation with one hyperedge $\{1,2\}$ of weight one. It is $\beta$-MPH for every $\beta\ge2$, and it is the instance on which no universally truthful budget-feasible mechanism has bounded approximation.
--
--   **Formalization Note** The agents $1,2$ are $0,1\in\mathrm{Fin}\,2$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §C.5, eq. (39), p.48 (PDF 50)

import Mathlib

namespace CompDesignBFM

namespace Supplement

/-- The 2-PH valuation (39) (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §C.5, eq. (39), p.48, PDF 50): on `N = {1, 2}`,
`v(∅) = v({1}) = v({2}) = 0` and `v({1, 2}) = 1` (one hyperedge `{1, 2}` of weight one).
**Formalization Note.** The agents `1, 2` are `0, 1 : Fin 2`, and `{1, 2}` is `Finset.univ`. -/
def pairValue (S : Finset (Fin 2)) : ℝ :=
  if S = Finset.univ then 1 else 0

end Supplement

end CompDesignBFM


