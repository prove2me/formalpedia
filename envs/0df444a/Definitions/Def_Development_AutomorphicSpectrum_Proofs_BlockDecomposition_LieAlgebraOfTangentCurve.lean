-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:32.504207+00:00
-- url     : https://prove2.me/theorems/0fa199cf-a5c3-4256-89cf-f7ce19d38493
-- title:
--   Lie Algebra Of Tangent Curve
-- statement:
--   Definitions and structural lemmas for Lie Algebra Of Tangent Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
namespace GlobalTheory.CompanionTheory.SmTangent
section Abstract
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A] [CompleteSpace A]
end Abstract
end GlobalTheory.CompanionTheory.SmTangent


