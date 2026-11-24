-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:09.763065+00:00
-- url     : https://prove2.me/theorems/49aea600-18d8-4240-907c-e5359b1b9186
-- title:
--   Norm Ball Volumes
-- statement:
--   Definitions and structural lemmas for Norm Ball Volumes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormBallVolumes.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def iv {k r : ℕ} (g : Mat k r) : Mat k r := Hpk k r * gᴴ * Hpk k r
end Formalism.FourierDecayAlt.P.NormBallVolumes
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.NormBallVolumes


