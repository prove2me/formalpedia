-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:54.281637+00:00
-- url     : https://prove2.me/theorems/289c6972-c949-4b96-87f3-9ba290ee5b57
-- title:
--   Raising Constant Eq Nabla Star
-- statement:
--   Definitions and structural lemmas for Raising Constant Eq Nabla Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RaisingConstantEqNablaStar.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
section lead
variable {R : Type*} [Ring R] [Algebra ℂ R]
def Lead (n : ℕ) (c : R) (f : ℂ → R) : Prop :=
  ∃ a : ℕ → R, ∀ Y, f Y = Y ^ n • c + ∑ i ∈ range n, Y ^ i • a i
variable {n m : ℕ} {c d : R} {f g : ℂ → R}
end lead
end Formalism.FourierDecayAlt.P.Mx5
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


