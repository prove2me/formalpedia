-- Prove2me | Definitions.Def_StarShapedRisk_Representation_Supplement_ExpectedShortfall
-- name    : StarShapedRisk_Representation_Supplement_ExpectedShortfall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:44:09.726938+00:00
-- url     : https://prove2.me/theorems/1adff917-645c-4860-8bc7-6ebee621c4ff
-- title:
--   Expected shortfall under the published VaR convention
-- statement:
--   For a probability $P$, a bounded measurable loss $X$ and $0<\alpha<1$, expected shortfall is
--   $$\operatorname{ES}_\alpha^P(X)=\frac1{1-\alpha}\int_\alpha^1\operatorname{VaR}_t^P(X)\,dt.$$
--   It averages upper loss quantiles using the paper's published VaR convention. The integral is a Lebesgue integral; including or excluding its endpoints has no effect. This definition supplies the functional in Theorem 4. Its total Lean value at $\alpha=1$ is zero and is never used by a theorem here.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2641, def-var-es

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

namespace StarShapedRisk.Representation.Supplement

/-- Expected shortfall at 0 < α < 1; endpoint values are not used in the targets. -/
noncomputable def ES {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (α : ℝ) (X : StarShapedRisk.LawInvariant.Positions Ω) : ℝ :=
  (1 - α)⁻¹ * ∫ t in Set.Icc α 1, StarShapedRisk.LawInvariant.VaR P t X.1

end StarShapedRisk.Representation.Supplement


