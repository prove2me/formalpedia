-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:42.661683+00:00
-- url     : https://prove2.me/theorems/7b1ebbea-1cf7-427f-b74e-f28a101d74fc
-- title:
--   Identity Of Principal Congruence
-- statement:
--   Definitions and structural lemmas for Identity Of Principal Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruence.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
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
namespace GlobalTheory.UnitLemma.CongruenceCayley
open GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
end GlobalTheory.UnitLemma.CongruenceCayley
namespace GlobalTheory.UnitLemma.CongruenceCayley
open GlobalTheory.UnitLemma.CayleyCase
end GlobalTheory.UnitLemma.CongruenceCayley


