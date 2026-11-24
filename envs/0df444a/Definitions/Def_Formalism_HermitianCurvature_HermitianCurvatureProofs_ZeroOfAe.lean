-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:11:33.279053+00:00
-- url     : https://prove2.me/theorems/90d4f291-6665-47bf-a813-7d4c02fe256d
-- title:
--   Zero Of Ae
-- statement:
--   Definitions and structural lemmas for Zero Of Ae, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroOfAe.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
namespace Formalism.FourierDecayAlt.P
namespace UnipotentHaarMeasurability
variable {k r : ℕ}
local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
end UnipotentHaarMeasurability
end Formalism.FourierDecayAlt.P


