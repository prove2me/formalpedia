-- Prove2me | Definitions.Def_BoundedNVAudit_Stakes_GeneralDemand
-- name    : BoundedNVAudit_Stakes_GeneralDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:30:36.89998+00:00
-- url     : https://prove2.me/theorems/374b1753-5226-454b-bcda-28687bbcbfea
-- title:
--   General demand with genuine real truncated sales
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be a demand density. It is nonnegative, Lebesgue integrable, has total mass one, and satisfies
--
--   $$\int_{\mathbb R}\max(-d,0)f(d)\,dd<\infty.$$
--
--   The last condition expresses existence of real truncated sales at every finite order. It places no condition on the positive demand mean, and includes the standard-normal demand used on pp. 587–588. Expected sales, profit, and the convex-hull decision domain are the published definitions, not new model fields. Their required properties are conclusions of the goal.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4):566–589, 2008, doi:10.1287/msom.1070.0200, §4, equation (3), printed p. 572 (PDF p. 7); canonical demand printed pp. 587–588 (PDF pp. 22–23)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_ExpFam_Logit

namespace BoundedNVAudit.Stakes

/-- General real demand in Su (2008), §4, printed p. 572, (3).
The negative-part condition expresses existence of real truncated sales at every order.
There is no restriction on the positive demand moment or on the sign of demand. -/
structure IsGeneralDemandDensity (f : ℝ → ℝ) : Prop where
  nonneg : ∀ d, 0 ≤ f d
  integrable : MeasureTheory.Integrable f
  mass_one : ∫ d, f d = 1
  negative_part : MeasureTheory.Integrable (fun d => max (-d) 0 * f d)

end BoundedNVAudit.Stakes


