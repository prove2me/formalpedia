-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:26.844297+00:00
-- url     : https://prove2.me/theorems/6a4058d9-8279-48e2-8922-29f157a38018
-- title:
--   Fourier Coefficients Of Vector Group
-- statement:
--   Definitions and structural lemmas for Fourier Coefficients Of Vector Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientsOfVectorGroup.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory FourierCoefficientMatrices FourierCubeVolume FourierCubeIntegral
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.FD


