-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:52.639103+00:00
-- url     : https://prove2.me/theorems/77f75d30-d82a-4256-a0d0-684df272e147
-- title:
--   Fderiv Fderiv Log Rho
-- statement:
--   Definitions and structural lemmas for Fderiv Fderiv Log Rho, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/FderivFderivLogRho.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace FSLevi
variable {J : Type} [Fintype J]
def reP (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj p)
def imaginary (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj p)
def nsq (z : J → ℂ) : ℝ := ∑ p, (reP p z ^ 2 + imaginary p z ^ 2)
def bil : (J → ℂ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) :=
  ∑ p, ((reP p).smulRight (reP p) + (imaginary p).smulRight (imaginary p))
end FSLevi
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel


