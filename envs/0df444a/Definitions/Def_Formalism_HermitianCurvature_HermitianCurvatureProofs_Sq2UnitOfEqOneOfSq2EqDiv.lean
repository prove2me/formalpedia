-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:06:39.468452+00:00
-- url     : https://prove2.me/theorems/db6a79e1-d28e-49ac-816b-c88abb8417eb
-- title:
--   Sq2 Unit Of Eq One Of Sq2 Eq Div
-- statement:
--   Definitions and structural lemmas for Sq2 Unit Of Eq One Of Sq2 Eq Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Sq2UnitOfEqOneOfSq2EqDiv.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Mathlib.Geometry.Manifold.PartitionOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def utv {k r m : ℕ} (ε T : ℝ) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ) (g : Mat k r) : Fin m → ℂ :=
  fun a => (Real.sqrt T : ℂ) * (Phh ε ((Gp g : ℝ) : ℂ) * om g a)
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


