-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_SoftFieldClauseIntensity
-- name    : KSATSingleFlip_Connect_SoftFieldClauseIntensity
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:38:19.687678+00:00
-- url     : https://prove2.me/theorems/e5f4fb10-4734-4c53-be5a-42f131782513
-- title:
--   Poisson clause-parameter intensity
-- statement:
--   The measure ρν is four times the pushforward under z↦1−q(z) of the soft-field measure weighted by cosh(z). It is the clause-parameter Poisson intensity in equation (4.3).
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KSATSingleFlip.Connect

/-- The clause-parameter intensity ρν(A)=4 ∫ 1_{1−q(z)∈A} cosh(z) dν(z). -/
def softClauseIntensity (ν : Measure ℝ) : Measure ℝ :=
  (4 : ℝ≥0∞) • Measure.map (fun z => 1-qOf z)
    (ν.withDensity fun z => ENNReal.ofReal (Real.cosh z))

end KSATSingleFlip.Connect


