-- Prove2me | Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
-- name    : D1Bound5_CoupledPhaseBounds_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:25:53.215667+00:00
-- url     : https://prove2.me/theorems/2769d3f6-ec75-47ba-9806-aec967657082
-- title:
--   Coupled Phase Bounds
-- statement:
--   Definitions for coupled phase bounds in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `phaseHalfPolynomial`, `phaseCritical`, `CoupledPhaseRow`.
-- source:
--   D1Bound5/CoupledPhaseBounds.lean, lines 7-7, SHA-256 14ad3644c7d0af80f0ec212461e5adea70bec57470ae7e0a8a0ee48d46ce9bc9; D1Bound5/CoupledPhaseBounds.lean, lines 8-8, SHA-256 14ad3644c7d0af80f0ec212461e5adea70bec57470ae7e0a8a0ee48d46ce9bc9; D1Bound5/CoupledPhaseBounds.lean, lines 108-110, SHA-256 14ad3644c7d0af80f0ec212461e5adea70bec57470ae7e0a8a0ee48d46ce9bc9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

section
namespace D1Bound5

noncomputable def phaseHalfPolynomial (q x : ℝ) : ℝ := (4-x^2)^2*(1+(1/q)^2+x/q)
noncomputable def phaseCritical (q x : ℝ) : ℝ := 5*x^2/q+4*(1+(1/q)^2)*x-4/q







noncomputable def CoupledPhaseRow (q F : ℝ) : Prop :=
  (q=8 ∧ F=269) ∨ (q=8/3 ∧ F=368) ∨ (q=12/7 ∧ F=540) ∨
  (q=3/2 ∧ F=637) ∨ (q=18/17 ∧ F=1121)





end D1Bound5
end


