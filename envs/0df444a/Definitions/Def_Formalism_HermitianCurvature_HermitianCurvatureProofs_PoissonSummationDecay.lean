-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:59.078741+00:00
-- url     : https://prove2.me/theorems/7d2f7a01-c30a-4b24-a1b3-7abd78dbb112
-- title:
--   Poisson Summation Decay
-- statement:
--   Definitions and structural lemmas for Poisson Summation Decay, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
section Summable
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
end Summable
section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]
noncomputable def gP (π : ι → V →L[ℝ] ℂ) (c : V) : ℝ := ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹
end
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


