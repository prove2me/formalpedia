-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:13:06.416277+00:00
-- url     : https://prove2.me/theorems/9a658f31-d154-4856-9170-5a2a5ad440b0
-- title:
--   Host Generator Pow Four Trace Norm Mod Eight
-- statement:
--   Definitions and structural lemmas for Host Generator Pow Four Trace Norm Mod Eight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HostGeneratorPowFourTraceNormModEight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory


