-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleIndicatorFunctions
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleIndicatorFunctions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:33.648987+00:00
-- url     : https://prove2.me/theorems/65311450-4408-43af-8a63-f4162800a132
-- title:
--   Admissible Indicator Functions
-- statement:
--   Definitions and structural lemmas for Admissible Indicator Functions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleIndicatorFunctions.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Classical in

def indFam : Fam E n N := fun Λ x => if ColsIn Λ x then 1 else 0
end
end GlobalTheory.SW


