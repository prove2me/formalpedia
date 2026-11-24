-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:32.193288+00:00
-- url     : https://prove2.me/theorems/3aac96ee-8f09-4df7-93b0-19ceb4db49cc
-- title:
--   Sphere Mean Calc
-- statement:
--   Definitions and structural lemmas for Sphere Mean Calc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
namespace SphereMean
def polyP (m : ℕ) (s : ℝ) : ℝ := ∑ j ∈ Finset.range (m + 1), (1 - s) ^ j / (m + 1)
def polyR (m : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (1 - (1 - s) ^ (j + 1)) / ((j + 1) * (m + 1))
def primG (m : ℕ) (s : ℝ) : ℝ := (1 - (1 - s) ^ (m + 1)) / (m + 1) * log s - polyR m s
end SphereMean
end
end GroundTheory.Heights₂.Heights


