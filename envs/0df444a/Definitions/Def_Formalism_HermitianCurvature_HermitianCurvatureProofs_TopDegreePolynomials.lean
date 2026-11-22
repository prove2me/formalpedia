-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:27.898468+00:00
-- url     : https://prove2.me/theorems/11e817a2-abcc-45a9-95bb-f3009eb3ad2b
-- title:
--   Top Degree Polynomials
-- statement:
--   Definitions and structural lemmas for Top Degree Polynomials, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.TopDegreePolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
end
end Formalism.FourierDecayAlt.P.TopDegreePolynomials
namespace Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.TopDegreePolynomials
end Formalism.FourierDecayAlt.P


