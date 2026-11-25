-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TwoPlaces
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TwoPlaces
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:13:59.24198+00:00
-- url     : https://prove2.me/theorems/e70c63e5-8d49-4d6f-9cd2-bf50f1026e07
-- title:
--   Two Places
-- statement:
--   Definitions and structural lemmas for Two Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TwoPlaces.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TwoPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_StatementW
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
namespace Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong HasJetBound OrbitsMul opAlong jetPairPoly)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D Formalism.L2.Th1.D.BiextensionAlongSeries
end Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
namespace Formalism.L2.Th1.D
end Formalism.L2.Th1.D


