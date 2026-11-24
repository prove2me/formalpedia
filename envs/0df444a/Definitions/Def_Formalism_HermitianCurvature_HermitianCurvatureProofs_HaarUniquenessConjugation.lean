-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:49.603979+00:00
-- url     : https://prove2.me/theorems/ba8ae1cb-4059-43ff-a83f-643ac90d02f6
-- title:
--   Haar Uniqueness Conjugation
-- statement:
--   Definitions and structural lemmas for Haar Uniqueness Conjugation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
def phi (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (u : UJ ε) : Mt k r :=
  (P⁻¹ * ((u : (Mat k r)ˣ) : Mat k r) * P : Mat k r)
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P


