-- Prove2me | Definitions.Def_EPRPharma_WelfareAtLeast
-- name    : EPRPharma_WelfareAtLeast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:07.694887+00:00
-- url     : https://prove2.me/theorems/86f47e5a-7ac3-4077-96ed-cb945595d9b1
-- title:
--   One model is at least as good as the other in maximal welfare
-- statement:
--   Model $P_1$ is at least as good as model $P_2$ if both have a maximal total welfare and $W_{P_1}^*\ge W_{P_2}^*$.
--
--   The planner "compares the expected total welfare of the EC vs. SR models and chooses the one that is higher"; the entries "SR" and "EC" of Table 2 are read as these weak comparisons ("weakly dominates", "at least as high", p. 19 and Online Appendix p. 5).
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 13; Table 2, p. 18; p. 19

import Mathlib
import Definitions.Def_EPRPharma_IsMaxWelfare

namespace EPRPharma

/-- **Model m₁ is total welfare maximizing (weakly) against model m₂.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 13: the planner "compares the
expected total welfare of the EC vs. SR models and chooses the one that is higher"; Table 2, p. 18,
and its discussion, p. 19 ("weakly dominates", "at least as high").
`WelfareAtLeast P m₁ m₂` says that both models have a maximal total welfare and that of m₁ is at
least that of m₂. -/
def WelfareAtLeast (P : Params) (m₁ m₂ : Model) : Prop :=
  ∃ v₁ v₂ : ℝ, IsMaxWelfare P m₁ v₁ ∧ IsMaxWelfare P m₂ v₂ ∧ v₂ ≤ v₁

end EPRPharma


