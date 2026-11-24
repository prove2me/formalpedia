-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:32:18.172998+00:00
-- url     : https://prove2.me/theorems/2509a0a7-1721-45be-b00f-3883b6757312
-- title:
--   Continuous Mul Mt
-- statement:
--   Definitions and structural lemmas for Continuous Mul Mt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
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
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
def mulMt {k r : ℕ} (s x : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r := fun i j => (Matrix.of s * Matrix.of x) i j
section Groups
variable {k r : ℕ}
end Groups
section Pi
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
end Pi
section Sigma
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Sigma
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity


