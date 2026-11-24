-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:45.139983+00:00
-- url     : https://prove2.me/theorems/fe7eba2f-4ed2-46e8-8943-5a0391815d23
-- title:
--   Triple Integrand Measurable
-- statement:
--   Definitions and structural lemmas for Triple Integrand Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
def Phi3 (e1 e2 : Mx k r → ℂ) (γi : Mx k r) (x : Formalism.QuantumDeterminants.Mt k r) (p q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ * ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ
end Formalism.FourierDecayAlt.P.S3dx4


