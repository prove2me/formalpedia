-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:28.203692+00:00
-- url     : https://prove2.me/theorems/2e24fbcc-4979-4eee-95cc-bf5363719cda
-- title:
--   Biextension Of Exp Spec
-- statement:
--   Definitions and structural lemmas for Biextension Of Exp Spec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionOfExpSpec.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add

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
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog thetaZ bSum linSub idM ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
namespace BiextensionSums
end BiextensionSums
open BiextensionSums
end Formalism.L2.Th1.D


