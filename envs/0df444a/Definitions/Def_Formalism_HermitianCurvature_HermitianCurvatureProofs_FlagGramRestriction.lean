-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T17:28:20.568647+00:00
-- url     : https://prove2.me/theorems/3ba1c2f1-56e2-4ad9-b204-e63a01826099
-- title:
--   Flag Gram Restriction
-- statement:
--   Definitions and structural lemmas for Flag Gram Restriction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagGramRestriction.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
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
namespace FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
def PhiH (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ h : B.Mat k r) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (C2.uMap k r z h) 0 0 (C2.uMap k r z' (γ⁻¹ * h * γ))
end FlagGramRestriction
end Formalism.FourierDecayAlt.P


