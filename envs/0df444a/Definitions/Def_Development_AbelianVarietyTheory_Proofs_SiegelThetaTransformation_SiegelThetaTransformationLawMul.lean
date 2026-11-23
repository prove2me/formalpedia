-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:34.712392+00:00
-- url     : https://prove2.me/theorems/b36d3819-948b-4228-b28d-3691bf7190dd
-- title:
--   Siegel Theta Transformation Law Mul
-- statement:
--   Definitions and structural lemmas for Siegel Theta Transformation Law Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.TransComp
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.SW.TransComp


