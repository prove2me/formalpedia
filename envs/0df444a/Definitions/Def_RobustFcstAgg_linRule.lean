-- Prove2me | Definitions.Def_RobustFcstAgg_linRule
-- name    : RobustFcstAgg_linRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:51.817201+00:00
-- url     : https://prove2.me/theorems/8ad83c17-58b3-4752-a8e8-43f6fe8903ab
-- title:
--   Linear intersection aggregation rule (Definition 6)
-- statement:
--   The **linear intersection aggregation rule** with coefficients $\beta=(\beta_S)_{1\le|S|\le d}$ has query collection $\mathcal Q_{\mathrm{inter}(d)}$ and outputs
--   $$f(\mathcal Q)=\sum_{1\le|S|\le d}\beta_S\,\mathrm{inter}(S).$$
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 6, p.9

import Mathlib
import Definitions.Def_RobustFcstAgg_InterIndex
import Definitions.Def_RobustFcstAgg_Rule
import Definitions.Def_RobustFcstAgg_interQuery

namespace RobustFcstAgg

/-- **Linear intersection aggregation rule.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 6, p.9: `𝒬 := Q_inter(d)` and
`f(𝒬) = Σ_{Q ∈ 𝒬} β_Q Q`. -/
def linRule (n d : ℕ) (β : InterIndex n d → ℝ) : Rule n where
  ι := InterIndex n d
  Q := fun S => interQuery S.1 S.2.1
  f := fun q => ∑ S, β S * q S
  measurable_f := by fun_prop

end RobustFcstAgg


