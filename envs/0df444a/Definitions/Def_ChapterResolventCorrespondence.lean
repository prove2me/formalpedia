-- Prove2me | Definitions.Def_ChapterResolventCorrespondence
-- name    : ChapterResolventCorrespondence
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T14:19:14.638717+00:00
-- url     : https://prove2.me/theorems/7079affd-8e81-4112-b2eb-3c72b0bf93fa
-- title:
--   Chapter ResolventCorrespondence
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterResolventCorrespondence.lean`): generated def bundle for ChapterResolventCorrespondence. See BookProof/ChapterResolventCorrespondence.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterResolventCorrespondence.lean

import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterA4
import Mathlib


/-!
# The resolvent correspondence: `T ↦ (1 + T)⁻¹` is a bijection onto the positive contractions

`BookProof.ChapterPositiveSquareRootUnique` attaches to every non-negative self-adjoint
linear relation `T` on a complex Hilbert space `F` the everywhere-defined bounded
operator `invCLM hT = (1 + T)⁻¹`, and shows that it is a positive contraction
(`invCLM_nonneg`, `invCLM_le_one`) from which `T` is recovered (`rel_eq_of_invCLM_eq`).

This chapter closes the correspondence in the other direction: **every** positive
contraction `R` (`0 ≤ R ≤ 1`) is the resolvent of one, and only one, non-negative
self-adjoint linear relation, namely

`relOfCLM R = {(R y, y − R y) : y ∈ F}`,

formally `R⁻¹ − 1`.  So `T ↦ (1 + T)⁻¹` is a bijection

`{non-negative self-adjoint linear relations on F} ≃ {R : F →L[ℂ] F | 0 ≤ R ≤ 1}`,

with inverse `R ↦ relOfCLM R` (`relOfCLM_invCLM`, `invCLM_relOfCLM`,
`existsUnique_isNonnegSelfAdjoint_invCLM_eq`).  Under it, the operators — the
single-valued relations — correspond to the *injective* positive contractions
(`singleValued_relOfCLM_iff`), and the domain of `T` is the range of `R`
(`mem_domain_relOfCLM_iff`).

The proof of non-negativity is the identity `R (1 − R) = (R^{1/2}(1−R)^{1/2})²`
(`mul_one_sub_eq_midOp_sq`), which makes `⟪R y, y − R y⟫ = ‖R^{1/2}(1−R)^{1/2} y‖²`
manifestly non-negative.
-/

namespace BookProof.ResolventCorrespondence

open BookProof.ClosureUniqueness BookProof.UnboundedPolar BookProof.PositiveSquareRoot
open BookProof.NonnegSquareRoot
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {R : F →L[ℂ] F} {T : Submodule ℂ (F × F)}

/-! ## The relation attached to a bounded operator -/

/-- A non-negative bounded operator is self-adjoint. -/
theorem isSelfAdjoint_of_nonneg {A : F →L[ℂ] F} (hA : 0 ≤ A) : IsSelfAdjoint A :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    ((ContinuousLinearMap.nonneg_iff_isPositive A).1 hA).1


/-- **`R⁻¹ − 1` as a linear relation**: the set of pairs `(R y, y − R y)`. -/
noncomputable def relOfCLM (R : F →L[ℂ] F) : Submodule ℂ (F × F) :=
  LinearMap.range (R.toLinearMap.prod ((1 : F →L[ℂ] F) - R).toLinearMap)

omit [CompleteSpace F] in
theorem mem_relOfCLM_iff {p : F × F} :
    p ∈ relOfCLM R ↔ ∃ y, R y = p.1 ∧ y - R y = p.2 := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simp [← hy], by simp [← hy]⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y, Prod.ext h1 (by simpa using h2)⟩

omit [CompleteSpace F] in
theorem mem_relOfCLM (R : F →L[ℂ] F) (y : F) : (R y, y - R y) ∈ relOfCLM R :=
  mem_relOfCLM_iff.2 ⟨y, rfl, rfl⟩

/-! ## `relOfCLM R` is non-negative and self-adjoint -/

/-- `R (1 − R) = M²` for `M = R^{1/2} (1 − R)^{1/2}`. -/
theorem mul_one_sub_eq_midOp_sq (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    R * (1 - R) = midOp R * midOp R := by
  have hS : sqrtOp R * sqrtOp R = R := sqrtOp_mul_self h0 h1
  have hD : coSqrtOp R * coSqrtOp R = 1 - R := coSqrtOp_mul_self h0 h1
  have hSD : sqrtOp R * coSqrtOp R = midOp R := sqrtOp_mul_coSqrtOp h0
  have hDS : coSqrtOp R * sqrtOp R = midOp R := coSqrtOp_mul_sqrtOp h0
  calc R * (1 - R) = (sqrtOp R * sqrtOp R) * (coSqrtOp R * coSqrtOp R) := by rw [hS, hD]
    _ = sqrtOp R * (sqrtOp R * coSqrtOp R) * coSqrtOp R := by
        simp only [mul_assoc]
    _ = sqrtOp R * (coSqrtOp R * sqrtOp R) * coSqrtOp R := by rw [hSD, hDS]
    _ = (sqrtOp R * coSqrtOp R) * (sqrtOp R * coSqrtOp R) := by
        simp only [mul_assoc]
    _ = midOp R * midOp R := by rw [hSD]

/-- **`R⁻¹ − 1` is symmetric.** -/
theorem relOfCLM_le_adjPairs (hR : IsSelfAdjoint R) : relOfCLM R ≤ adjPairs (relOfCLM R) := by
  intro p hp q hq
  obtain ⟨y, hy1, hy2⟩ := mem_relOfCLM_iff.1 hp
  obtain ⟨z, hz1, hz2⟩ := mem_relOfCLM_iff.1 hq
  rw [← hy1, ← hy2, ← hz1, ← hz2, inner_sub_left, inner_sub_right,
    ← inner_isSelfAdjoint_left hR z y]

omit [CompleteSpace F] in
/-- **`1 + (R⁻¹ − 1)` is surjective.** -/
theorem exists_mem_relOfCLM_add (R : F →L[ℂ] F) (h : F) :
    ∃ p ∈ relOfCLM R, p.1 + p.2 = h :=
  ⟨(R h, h - R h), mem_relOfCLM R h, by simp⟩

/-- **`R⁻¹ − 1` is self-adjoint.** -/
theorem adjPairs_relOfCLM (hR : IsSelfAdjoint R) : adjPairs (relOfCLM R) = relOfCLM R :=
  adjPairs_eq_self_of_symmetric_of_surjective (relOfCLM_le_adjPairs hR)
    (exists_mem_relOfCLM_add R)

/-- **The quadratic form of `R⁻¹ − 1` is `‖M y‖²`** for `M = R^{1/2}(1−R)^{1/2}` and
`y = x + T x` the point of `F` the pair comes from. -/
theorem inner_relOfCLM (h0 : 0 ≤ R) (h1 : R ≤ 1) {p : F × F} (hp : p ∈ relOfCLM R) :
    (inner ℂ p.1 p.2 : ℂ) = ((‖midOp R (p.1 + p.2)‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨y, hy1, hy2⟩ := mem_relOfCLM_iff.1 hp
  have hR : IsSelfAdjoint R := isSelfAdjoint_of_nonneg h0
  have hM : IsSelfAdjoint (midOp R) := isSelfAdjoint_of_nonneg (midOp_nonneg R)
  have hkey : (inner ℂ (R y) (y - R y) : ℂ) = ((‖midOp R y‖ ^ 2 : ℝ) : ℂ) := by
    have happ : (R * (1 - R)) y = R (y - R y) := by
      simp [ContinuousLinearMap.mul_apply]
    have h2 : (inner ℂ (R y) (y - R y) : ℂ) = inner ℂ y ((R * (1 - R)) y) := by
      rw [happ]
      exact inner_isSelfAdjoint_left hR y (y - R y)
    rw [h2, mul_one_sub_eq_midOp_sq h0 h1]
    have h3 : ((midOp R * midOp R : F →L[ℂ] F)) y = midOp R (midOp R y) := rfl
    rw [h3, ← inner_isSelfAdjoint_left hM y (midOp R y), inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsum : R y + (y - R y) = y := by abel
  rw [← hy1, ← hy2, hsum]
  exact hkey

/-- **`R⁻¹ − 1 ≥ 0`.** -/
theorem relOfCLM_quadForm_nonneg (h0 : 0 ≤ R) (h1 : R ≤ 1) {p : F × F} (hp : p ∈ relOfCLM R) :
    0 ≤ (inner ℂ p.1 p.2 : ℂ).re := by
  rw [inner_relOfCLM h0 h1 hp, Complex.ofReal_re]
  positivity

/-- **`R⁻¹ − 1` is a non-negative self-adjoint linear relation.** -/
theorem isNonnegSelfAdjoint_relOfCLM (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    IsNonnegSelfAdjoint (relOfCLM R) where
  adj := adjPairs_relOfCLM (isSelfAdjoint_of_nonneg h0)
  nonneg := fun _ hp => relOfCLM_quadForm_nonneg h0 h1 hp

/-! ## The two constructions are mutually inverse -/

/-- **`(1 + (R⁻¹ − 1))⁻¹ = R`.** -/
theorem invCLM_relOfCLM (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    invCLM (isNonnegSelfAdjoint_relOfCLM h0 h1) = R := by
  ext h
  exact invCLM_eq_of_mem _ (mem_relOfCLM R h)

/-- **`((1 + T)⁻¹)⁻¹ − 1 = T`.** -/
theorem relOfCLM_invCLM (hT : IsNonnegSelfAdjoint T) : relOfCLM (invCLM hT) = T :=
  rel_eq_of_invCLM_eq
    (isNonnegSelfAdjoint_relOfCLM (invCLM_nonneg hT) (invCLM_le_one hT)) hT
    (invCLM_relOfCLM (invCLM_nonneg hT) (invCLM_le_one hT))

/-- **The resolvent correspondence.**  Every positive contraction is the resolvent
`(1 + T)⁻¹` of exactly one non-negative self-adjoint linear relation `T`. -/
theorem existsUnique_isNonnegSelfAdjoint_invCLM_eq (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    ∃! T : Submodule ℂ (F × F), ∃ hT : IsNonnegSelfAdjoint T, invCLM hT = R := by
  refine ⟨relOfCLM R, ⟨isNonnegSelfAdjoint_relOfCLM h0 h1, invCLM_relOfCLM h0 h1⟩, ?_⟩
  rintro S ⟨hS, hSR⟩
  exact rel_eq_of_invCLM_eq hS (isNonnegSelfAdjoint_relOfCLM h0 h1)
    (by rw [hSR, invCLM_relOfCLM h0 h1])

/-! ## Operators correspond to injective contractions -/

omit [CompleteSpace F] in
/-- **`R⁻¹ − 1` is single-valued (an operator) exactly when `R` is injective.** -/
theorem singleValued_relOfCLM_iff :
    (∀ w : F, ((0 : F), w) ∈ relOfCLM R → w = 0) ↔ Function.Injective R := by
  constructor
  · intro hsv y z hyz
    have h0 : R (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    have hmem : ((0 : F), y - z) ∈ relOfCLM R := by
      have := mem_relOfCLM R (y - z)
      rwa [h0, sub_zero] at this
    exact sub_eq_zero.1 (hsv _ hmem)
  · intro hinj w hw
    obtain ⟨y, hy1, hy2⟩ := mem_relOfCLM_iff.1 hw
    simp only at hy1 hy2
    have hy0 : y = 0 := by
      have : R y = R 0 := by rw [hy1, map_zero]
      exact hinj this
    rw [← hy2, hy0, map_zero, sub_zero]

omit [CompleteSpace F] in
/-- The domain of `R⁻¹ − 1` is the range of `R`. -/
theorem mem_domain_relOfCLM_iff {x : F} :
    (∃ w, (x, w) ∈ relOfCLM R) ↔ x ∈ LinearMap.range (R : F →ₗ[ℂ] F) := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy1, -⟩ := mem_relOfCLM_iff.1 hw
    exact ⟨y, hy1⟩
  · rintro ⟨y, hy⟩
    exact ⟨y - R y, mem_relOfCLM_iff.2 ⟨y, hy, rfl⟩⟩

end BookProof.ResolventCorrespondence


