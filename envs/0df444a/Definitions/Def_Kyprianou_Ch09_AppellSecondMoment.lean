-- Prove2me | Definitions.Def_Kyprianou_Ch09_AppellSecondMoment
-- name    : Kyprianou_Ch09_AppellSecondMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:15:48.150462+00:00
-- url     : https://prove2.me/theorems/36311e75-38d2-49b6-8336-613fcc198aa8
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner AppellSecondMoment
-- statement:
--   Appell moment and integrability-related definitions. This source Definition module provides the actual declarations: AppellSecondMoment. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_Appell
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- Second-degree finite-moment mean-value property. This proves the
nontrivial n=2 algebra for a genuine finite-support probability law
(weights of mass one) without assuming exponential moments. -/
theorem appellTwo_finite_mean {n : ℕ} (w y : Fin n → ℝ)
    (m variance x : ℝ)
    (hmass : ∑ i, w i = 1)
    (hm : ∑ i, w i * y i = m)
    (hv : ∑ i, w i * (y i - m) ^ 2 = variance) :
    (∑ i, w i * appellTwo m variance (x + y i)) = x ^ 2 := by
  have hcenter : (∑ i, w i * (y i - m)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul]
    rw [hm, hmass]
    ring
  calc
    (∑ i, w i * appellTwo m variance (x + y i)) =
        (∑ i, (w i * x ^ 2 + 2 * x * (w i * (y i - m)) +
          w i * (y i - m) ^ 2 - w i * variance)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [appellTwo]
            ring
    _ = (∑ i, w i) * x ^ 2 +
          2 * x * (∑ i, w i * (y i - m)) +
          (∑ i, w i * (y i - m) ^ 2) -
          (∑ i, w i) * variance := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            simp only [← Finset.sum_mul, ← Finset.mul_sum]
    _ = x ^ 2 := by
          rw [hmass, hcenter, hv]
          ring

end Kyprianou.Ch09.B1


