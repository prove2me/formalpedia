-- Prove2me | Definitions.Def_StarShapedRisk_Representation_Supplement_LawPositionSpace
-- name    : StarShapedRisk_Representation_Supplement_LawPositionSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:46:54.464537+00:00
-- url     : https://prove2.me/theorems/85d10071-4222-4b5e-95b6-1ca864163169
-- title:
--   The bounded measurable position space as a PositionSpace
-- statement:
--   The published space $\mathcal X$ of bounded measurable functions is a linear space containing all constants. Package this same carrier as a position space so the published average, supremum, infimum and inf-convolution apply directly:
--   $$\mathcal X=\{X:\Omega\to\mathbb R\mid X\text{ measurable and bounded}\}.$$
--   This is an interface to the existing aggregation operators, with the same functions, constants, pointwise addition and scalar multiplication. It introduces no replacement risk-measure axioms. As in the published law-invariant mission, almost-sure quotienting is represented using bounded measurable representatives; law invariance or SSD-consistency makes null modifications immaterial in the targets.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2646, sa-linf

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation
import Definitions.Def_StarShapedRisk_LawInvariant_Model

namespace StarShapedRisk.Representation.Supplement

/-- The published bounded measurable carrier, packaged for the published aggregation operators. -/
def lawPositionSpace (Ω : Type*) [MeasurableSpace Ω] : PositionSpace Ω where
  carrier := StarShapedRisk.LawInvariant.Positions Ω
  const_mem := fun c => ⟨measurable_const, |c|, fun _ => le_rfl⟩
  bounded := fun _ hX => hX.2

end StarShapedRisk.Representation.Supplement


