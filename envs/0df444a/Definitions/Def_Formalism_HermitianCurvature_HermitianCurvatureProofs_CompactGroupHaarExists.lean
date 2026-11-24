-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:47.073802+00:00
-- url     : https://prove2.me/theorems/0328701d-ba2f-4f44-8ebf-e8de0cb0b2c2
-- title:
--   Compact Group Haar Exists
-- statement:
--   Definitions and structural lemmas for Compact Group Haar Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
namespace Formalism.FourierDecayAlt.P.B2x2
def mid (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : Prop := 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
def blk (k r' : ℕ) (x : Mat k (1 + r')) : Mat k r' := Matrix.of fun s t => x (levPos k 1 r' s) (levPos k 1 r' t)
end Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


