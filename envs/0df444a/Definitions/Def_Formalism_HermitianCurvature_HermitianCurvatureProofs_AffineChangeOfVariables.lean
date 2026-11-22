-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:12.603777+00:00
-- url     : https://prove2.me/theorems/6ea00825-7b87-4936-a2bd-7d7482ac0bfb
-- title:
--   Affine Change Of Variables
-- statement:
--   Definitions and structural lemmas for Affine Change Of Variables, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AffineChangeOfVariables.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace Formalism.FourierDecayAlt.P.G3
noncomputable def al (β : ℂ) : ℂ := -((starRingEnd ℂ) β) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
instance (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
end Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3
end Formalism.FourierDecayAlt.P


