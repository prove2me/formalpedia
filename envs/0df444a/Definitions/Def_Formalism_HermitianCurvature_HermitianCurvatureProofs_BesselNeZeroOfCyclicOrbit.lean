-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:47.284189+00:00
-- url     : https://prove2.me/theorems/4a8c6749-69be-4d85-ba9f-7896cddf2f57
-- title:
--   Bessel Ne Zero Of Cyclic Orbit
-- statement:
--   Definitions and structural lemmas for Bessel Ne Zero Of Cyclic Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P
open PI.UpqRep
namespace TranslationBesselVanishing
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def mulRightCLM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ]
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => h * g
      map_add' := fun a b => Matrix.add_mul a b g
      map_smul' := fun c a => by simp [Matrix.smul_mul] }
end TranslationBesselVanishing
end Formalism.FourierDecayAlt.P


