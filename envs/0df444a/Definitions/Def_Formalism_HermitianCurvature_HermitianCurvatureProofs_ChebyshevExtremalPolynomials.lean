-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:46.783509+00:00
-- url     : https://prove2.me/theorems/a7e24638-fbef-4db5-9540-3a8650838aeb
-- title:
--   Chebyshev Extremal Polynomials
-- statement:
--   Definitions and structural lemmas for Chebyshev Extremal Polynomials, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
noncomputable def nd (n : ℕ) (j : Fin (n + 1)) : ℝ := Chebyshev.node n j
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


