-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:29:42.098185+00:00
-- url     : https://prove2.me/theorems/55e37487-abf8-45de-abf2-e69f2c8d7868
-- title:
--   Lie Decomposition Local
-- statement:
--   Definitions and structural lemmas for Lie Decomposition Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def EZ (Z : Mat k r) (Φ : Mat k r → E) : Mat k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) Φ g + Complex.I • RdV (hpart2 (Hpk k r) Z) Φ g
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal


