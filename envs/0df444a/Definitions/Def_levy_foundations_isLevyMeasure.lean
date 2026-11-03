-- Prove2me | Definitions.Def_levy_foundations_isLevyMeasure
-- name    : levy_foundations_isLevyMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:50:17.781719+00:00
-- url     : https://prove2.me/theorems/bde15da2-475b-47df-a74d-f67937e57991
-- title:
--   Definition of a real-valued Lévy measure
-- statement:
--   A measure ν on the real line is a Lévy measure when it assigns zero mass to the origin and the integral of min(1,x²) against ν is finite.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L46-L48. Foundational jump-intensity condition. The Prove2Me statement and namespace are independently authored and require verification.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
namespace LevyFoundations
def isLevyMeasure (ν : Measure ℝ) : Prop :=
  ν {0} = 0 ∧ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤
end LevyFoundations


