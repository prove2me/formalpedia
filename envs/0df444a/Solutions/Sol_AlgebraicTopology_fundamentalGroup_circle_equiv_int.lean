-- Prove2me | solution 1 for AlgebraicTopology.fundamentalGroup_circle_equiv_int
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:28:13.334918+00:00
-- url     : https://prove2.me/submissions/5035a378-bae7-4983-987e-e8c2150fb9ab

import Mathlib

open AddSubgroup AddCircle

/-- Elements of `zmultiples (1:ℝ)` are exactly the integers, so the subgroup is `ℤ`. -/
noncomputable def zmultiplesOneEquivInt : zmultiples (1:ℝ) ≃+ ℤ where
  toFun x := ⌊(x : ℝ)⌋
  invFun n := ⟨(n : ℝ), ⟨n, by simp⟩⟩
  left_inv := by
    rintro ⟨x, n, rfl⟩
    have h : (n • (1:ℝ)) = (n : ℝ) := by simp
    simp [h]
  right_inv := by intro n; simp
  map_add' := by
    rintro ⟨x, m, rfl⟩ ⟨y, n, rfl⟩
    have hm : (m • (1:ℝ)) = (m : ℝ) := by simp
    have hn : (n • (1:ℝ)) = (n : ℝ) := by simp
    simp [hm, hn, ← Int.cast_add, Int.floor_intCast (R := ℝ)]

/-- **The fundamental group of the circle is `ℤ`.** -/
noncomputable def fundamentalGroupAddCircleEquivInt :
    FundamentalGroup (AddCircle (1:ℝ)) 0 ≃* Multiplicative ℤ :=
  ((AddCircle.isAddQuotientCoveringMap_coe (1:ℝ)).fundamentalGroupEquiv
      (⟨0, by simp⟩ : ((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' {0})).trans
    ((MulOpposite.opMulEquiv (M := Multiplicative (zmultiples (1:ℝ)))).symm.trans
      (AddEquiv.toMultiplicative zmultiplesOneEquivInt))

theorem solution :
    Nonempty (FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ) :=
  ⟨fundamentalGroupAddCircleEquivInt⟩
