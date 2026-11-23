-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:25.965967+00:00
-- url     : https://prove2.me/theorems/2f612e19-80b5-4d9c-929f-025fa703632a
-- title:
--   Rect Int Eq Zero Of Differentiable On
-- statement:
--   Definitions and structural lemmas for Rect Int Eq Zero Of Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)
def rectBdry (z w : ℂ) : Set ℂ :=
  {s | (s.re ∈ uIcc z.re w.re ∧ (s.im = z.im ∨ s.im = w.im)) ∨
       (s.im ∈ uIcc z.im w.im ∧ (s.re = z.re ∨ s.re = w.re))}
def rectOpen (z w : ℂ) : Set ℂ := {s | z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im}
def rectClosed (z w : ℂ) : Set ℂ := Icc z.re w.re ×ℂ Icc z.im w.im
end PI.EF.Rect


