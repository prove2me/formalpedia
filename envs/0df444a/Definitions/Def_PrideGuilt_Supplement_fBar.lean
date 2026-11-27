-- Prove2me | Definitions.Def_PrideGuilt_Supplement_fBar
-- name    : PrideGuilt_Supplement_fBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:23:11.742821+00:00
-- url     : https://prove2.me/theorems/9c399bf0-a6a9-4568-bed1-d7d8cee3865d
-- title:
--   Highest affordable recycling reward $\bar f=\max(f_p,f_m)$
-- statement:
--   The highest affordable recycling reward is
--
--   $$
--   \bar f\;=\;\max(f_p,f_m),
--   $$
--
--   with $f_p$ and $f_m$ as defined above. Propositions 2 and 3 compare it with the recycling thresholds of Lemma 1.
--
--   **Formalization Note** At $b_1=b_0$ it inherits the convention of $f_p$ (division by zero gives $0$).
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), §4, p.13

import Mathlib
import Definitions.Def_PrideGuilt_Supplement_fP
import Definitions.Def_PrideGuilt_Supplement_fM

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The highest affordable recycling reward, `f̄ ≡ max(f_p, f_m)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, §4, p.13 (PDF 14).

**Formalization Note.** Inherits the convention of `fP` at `b₁ = b₀`. -/
noncomputable def fBar (P : Params) (γG : ℝ) : ℝ := max (fP P) (fM P γG)

end PrideGuilt.Supplement


