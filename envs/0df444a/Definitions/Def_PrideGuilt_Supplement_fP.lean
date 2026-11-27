-- Prove2me | Definitions.Def_PrideGuilt_Supplement_fP
-- name    : PrideGuilt_Supplement_fP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:21:46.357525+00:00
-- url     : https://prove2.me/theorems/9142a4fb-5f75-40ae-a4c3-f426f58be1c8
-- title:
--   Reward $f_p$, the highest reward compatible with perfect recycling
-- statement:
--   With the demand coefficients $b_0,b_1$, the net recycling cost $c_r$ and the cost saving $\Delta c$,
--
--   $$
--   f_p\;=\;\frac{\Delta c-b_1c_r/b_0}{1-b_1/b_0}.
--   $$
--
--   The paper describes $f_p$ as the highest reward the manufacturer can offer while inducing perfect recycling and still gaining from remanufacturing.
--
--   **Formalization Note** The formula divides by $1-b_1/b_0$, which vanishes when $b_1=b_0$ (allowed by the standing assumptions); Lean's division then returns $0$, a value the paper never assigns. Statements that use $f_p$ either assume $b_1<b_0$ or hold on a region that is empty when $b_1=b_0$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), §4, p.13

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The highest reward compatible with perfect recycling, `f_p ≡ (Δc − b₁c_r/b₀)/(1 − b₁/b₀)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, §4, p.13 (PDF 14).

**Formalization Note.** The formula divides by `1 − b₁/b₀`, which is `0` when `b₁ = b₀` (allowed
by the standing assumptions); Lean's division then returns `0`, a value the paper never assigns.
Every statement that uses `f_p` either guards against `b₁ = b₀` or holds on a region that is
empty when `b₁ = b₀`. -/
noncomputable def fP (P : Params) : ℝ := (dc P - P.b1 * cr P / P.b0) / (1 - P.b1 / P.b0)

end PrideGuilt.Supplement


