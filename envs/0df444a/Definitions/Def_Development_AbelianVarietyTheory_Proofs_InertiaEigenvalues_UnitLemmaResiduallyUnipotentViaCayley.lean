-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:42:59.72034+00:00
-- url     : https://prove2.me/theorems/04fd5d81-059f-44f1-9b0e-63792feb89ee
-- title:
--   Unit Lemma Residually Unipotent Via Cayley
-- statement:
--   Definitions and structural lemmas for Unit Lemma Residually Unipotent Via Cayley, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
def withG (B : InvAlg K) (Y : B.A) : InvAlg K := { B with g := Y }
end GlobalTheory.UnitLemma.CayleyCase


