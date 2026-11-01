-- Prove2me | Definitions.Def_CloudCostOpt_fDP
-- name    : CloudCostOpt_fDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:03:49.506898+00:00
-- url     : https://prove2.me/theorems/5fad52ea-94de-49d8-af2a-cbf1ccd2c626
-- title:
--   Recursion values $f_i(s,l)$
-- statement:
--   The recursion values $f_i(s,l)=g_i(\delta_i-s,l)$ of p.13. For $s\ge\delta_i$ this is the late value $f^{Late}_i(l)=(L_i-l)\min_j(R_j+W_i)/\beta_{i,j}$ of Lemma 1; for $s<\delta_i$ it satisfies the recursion of p.13.
--
--   **Formalization Note** $\delta_i-s$ is natural-number subtraction, which is $0$ exactly when $s\ge\delta_i$, the late regime.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, pp.12–13

import Mathlib
import Definitions.Def_CloudCostOpt_fDPToGo

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The recursion values `fᵢ(s, l)`** of p.13: `fDPToGo` at `k = δᵢ − s` periods to the
deadline; for `s ≥ δᵢ` this is the late value `f^Late_i(l)` (Lemma 1).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, pp.12–13. -/
noncomputable def fDP (S : System) (i : Fin S.I) (s l : ℕ) : ℝ :=
  fDPToGo S i (S.δ i - s) l

end CloudCostOpt


