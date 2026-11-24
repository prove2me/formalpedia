-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:06:50.4718+00:00
-- url     : https://prove2.me/theorems/ed32780d-f272-4fdd-97a7-cf77ecd2091a
-- title:
--   Conjugation Invariance Every Setting
-- statement:
--   Definitions and structural lemmas for Conjugation Invariance Every Setting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
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
namespace Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section form
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
end form
def lastI (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩
end Formalism.FourierDecayAlt.P.B2x4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P


