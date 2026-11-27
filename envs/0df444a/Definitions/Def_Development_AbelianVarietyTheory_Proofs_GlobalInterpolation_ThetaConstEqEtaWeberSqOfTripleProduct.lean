-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaConstEqEtaWeberSqOfTripleProduct
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaConstEqEtaWeberSqOfTripleProduct
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:39.856545+00:00
-- url     : https://prove2.me/theorems/46b08a1b-084d-4faf-becf-ab8de2fda843
-- title:
--   Theta Const Eq Eta Weber Sq Of Triple Product
-- statement:
--   Definitions and structural lemmas for Theta Const Eq Eta Weber Sq Of Triple Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ThetaConstEqEtaWeberSqOfTripleProduct.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
namespace GlobalTheory.ThetaWeberProof
open GlobalTheory.ThetaWeberRoad GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
end GlobalTheory.ThetaWeberProof


