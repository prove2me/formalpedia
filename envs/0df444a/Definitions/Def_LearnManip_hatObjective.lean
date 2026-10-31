-- Prove2me | Definitions.Def_LearnManip_hatObjective
-- name    : LearnManip_hatObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:34.695861+00:00
-- url     : https://prove2.me/theorems/1087c7bd-b477-4395-adb7-aca17433f0dc
-- title:
--   Objective of the finite-stage iteration $\hat G_{k+1}$
-- statement:
--   For a function $g(s,c)$, the objective of the iteration of (EC.16) at stage $k+1$ and quantity $q$:
--   $$-cq+\alpha g\bigl(\tfrac{s}{1+sq},c\eta\bigr)+\frac{A_{k+1}^2\,\sigma^2_{\mu^q}}{2\gamma},\qquad A_{k+1}=\sum_{j=0}^k\alpha^j.$$
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (EC.16), p.ec9 (PDF 48), corrected

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_postVar
import Definitions.Def_LearnManip_meanVar
import Definitions.Def_LearnManip_geomSum

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The objective of the finite-stage iteration `Ĝ_{k+1}` of (EC.16), p.ec9 (PDF 48), of Keppo, Kim,
Zhang (SSRN 3465030, 2021-09-04): `−c q + α g(s/(1+sq), cη) + (∑_{j≤k} α^j)² σ²_{μ^q} / (2γ)`. -/
noncomputable def hatObjective (P : Params) (k : ℕ) (g : ℝ≥0 → ℝ≥0 → ℝ) (s c q : ℝ≥0) : ℝ :=
  -((c : ℝ) * q) + (P.α : ℝ) * g (postVar s q) (c * P.η)
    + (geomSum P (k + 1)) ^ 2 * (meanVar s q : ℝ) / (2 * (P.γ : ℝ))

end LearnManip


