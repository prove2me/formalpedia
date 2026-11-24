-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:45:40.544796+00:00
-- url     : https://prove2.me/theorems/d52097b4-6d99-4228-af24-eb3334894d54
-- title:
--   Sandwich Rho Action
-- statement:
--   Definitions and structural lemmas for Sandwich Rho Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
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
namespace Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def sandw (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp P).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip Q)).restrictScalars ℝ)
end Formalism.FourierDecayAlt.P.SandwichRhoAction


