-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:58.744852+00:00
-- url     : https://prove2.me/theorems/7cd562a2-fcf9-442c-aebe-ea022b9ddb9e
-- title:
--   Word Monic Extraction
-- statement:
--   Definitions and structural lemmas for Word Monic Extraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
end
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
noncomputable def letterVal (Ξ : Sesq M) (D : Dat R) (y : ℝ) (x x' : M) : ℂ :=
  Ξ ((evR D.B y + algebraMap ℂ R D.s * evR D.A y) • x) (evR D.Av (y + 1) • x') -
    Ξ (evR D.A y • x) (evR D.Bv (y + 1) • x')
end
end Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
end Formalism.FourierDecayAlt.P


