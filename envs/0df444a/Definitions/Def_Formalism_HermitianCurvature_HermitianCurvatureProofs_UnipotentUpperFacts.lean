-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:10:57.980346+00:00
-- url     : https://prove2.me/theorems/13c0af22-4f12-421f-9e50-b42374ec64ef
-- title:
--   Unipotent Upper Facts
-- statement:
--   Definitions and structural lemmas for Unipotent Upper Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P
namespace UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
section gen
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
end gen
variable {k r : ℕ}
end UnipotentUpperFacts
end Formalism.FourierDecayAlt.P


