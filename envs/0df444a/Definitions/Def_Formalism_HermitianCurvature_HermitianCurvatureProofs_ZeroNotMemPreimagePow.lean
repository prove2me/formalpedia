-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:23:48.211716+00:00
-- url     : https://prove2.me/theorems/22b6581d-5069-5fd8-aad6-96fddfa95179
-- title:
--   Zero Not Mem Preimage Pow
-- statement:
--   Definitions and structural lemmas for Zero Not Mem Preimage Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
def ann (n : ℕ) : Set ℂ := {D | ((n : ℝ) + 1)⁻¹ ≤ ‖D‖ ∧ ‖D‖ ≤ (n : ℝ) + 1}
section ss
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end ss
end
end Formalism.FourierDecayAlt.P.PBK


