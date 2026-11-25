-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_JetsInOfOneVariable
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_JetsInOfOneVariable
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:36:43.25541+00:00
-- url     : https://prove2.me/theorems/d63c384f-aa03-4de2-b8d4-5af1e11331b8
-- title:
--   Jets In Of One Variable
-- statement:
--   Definitions and structural lemmas for Jets In Of One Variable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/JetsInOfOneVariable.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp mfact)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair IsOneUnit jet)
open Formalism.L2.Th1.G (JetsIn JetsIn1)
open CompatibleChartOperations
namespace JetIntegrality
variable {K : Type} [Field K] {n : Type}
end JetIntegrality
end Formalism.L2.Th1.E


