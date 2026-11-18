-- Prove2me | Definitions.Def_Kyprianou_Ch09_AppellExpectation
-- name    : Kyprianou_Ch09_AppellExpectation
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:16:02.003213+00:00
-- url     : https://prove2.me/theorems/66e586b2-bc5b-4836-978b-942566ae371a
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner AppellExpectation
-- statement:
--   Expected Appell polynomial identities needed by the source statements. This source Definition module provides the actual declarations: AppellExpectation. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- Source-faithful degree-one Appell mean value for an arbitrary real
integrable nonnegative random variable on a genuine probability space.
This is a full source-n=1 technical leaf of Lemma 9.8 (general n Open). -/
theorem centeredAppell_first_mean_value
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Integrable Y P)
    (m x : ℝ) (hm : (∫ ω, Y ω ∂P) = m) :
    (∫ ω, ((x + Y ω - m) : ℝ) ∂P) = x := by
  have hfun :
      (fun ω : Ω => x + Y ω - m) =
        (fun ω : Ω => (x - m) + Y ω) := by
    funext ω
    ring
  rw [hfun, integral_add (integrable_const _) hY]
  simp [hm]

/-- Exact derivative and centring of the first Appell polynomial
requires only the finite first moment, no Laplace MGF. -/
theorem centeredAppell_first_centered
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    (∫ ω, (Y ω - ∫ ξ, Y ξ ∂P) ∂P) = 0 := by
  have h := centeredAppell_first_mean_value P Y hY (∫ ω, Y ω ∂P) 0 rfl
  simpa using h

end Kyprianou.Ch09.B1


