-- Prove2me | Definitions.Def_PCLAssort_LP9Objective
-- name    : PCLAssort_LP9Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:07.222128+00:00
-- url     : https://prove2.me/theorems/3db4bb5a-57ca-421e-926a-0b816fd37a5e
-- title:
--   Objective of the LP (9)
-- statement:
--   For edge weights $w$, the objective of the linear program (9) at a point $(x,y)$ is
--
--   $$
--   \sum_{(i,j)\in E} w_{ij}\,y_{ij}.
--   $$
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.3.1, LP (9), p.794 (PDF p.10)

import Mathlib

namespace PCLAssort

/-- Objective `∑_{(i,j) ∈ E} w_ij · y_ij` of LP (9) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.3.1, p.794), evaluated at a point
`p = (x, y)`. -/
def LP9Objective {V : Type} (E : Finset (V × V)) (w : V × V → ℝ) (p : (V → ℝ) × (V × V → ℝ)) : ℝ :=
  ∑ e ∈ E, w e * p.2 e

end PCLAssort


