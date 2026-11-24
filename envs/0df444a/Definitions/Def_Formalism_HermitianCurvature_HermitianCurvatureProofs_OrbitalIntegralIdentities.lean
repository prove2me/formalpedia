-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralIdentities
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralIdentities
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:10.204521+00:00
-- url     : https://prove2.me/theorems/1e4ff4c2-64a7-4216-8c41-9b7a4e10bf5c
-- title:
--   Orbital Integral Identities
-- statement:
--   Definitions and structural lemmas for Orbital Integral Identities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralIdentities.lean

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable [FiniteDimensional ℂ Wp]
end
end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


