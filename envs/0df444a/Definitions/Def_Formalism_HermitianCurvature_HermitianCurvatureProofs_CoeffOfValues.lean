-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoeffOfValues
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CoeffOfValues
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:14.88856+00:00
-- url     : https://prove2.me/theorems/e7b81e2e-a08c-4989-a3ba-24b1afcbfb95
-- title:
--   Coeff Of Values
-- statement:
--   Definitions and structural lemmas for Coeff Of Values, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
section vand
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
def vN (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.vandermonde fun m : Fin (d + 1) => ((m : ℕ) : ℂ)
end vand
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral


