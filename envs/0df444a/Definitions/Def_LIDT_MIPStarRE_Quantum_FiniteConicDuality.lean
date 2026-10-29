-- Prove2me | Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
-- name    : LIDT_MIPStarRE_Quantum_FiniteConicDuality
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:19.744416+00:00
-- url     : https://prove2.me/theorems/ac05ca3f-2107-4b35-86fe-475af48694d6
-- title:
--   LIDT definitions: Quantum / FiniteConicDuality
-- statement:
--   This bundle provides the finite-dimensional conic separation layer behind the functional duality argument. A separator on a constraint-objective product is decomposed, normalized when its objective coefficient is negative, and used to establish feasibility and a primal-dual equality under fiberwise attainment.
--
--   Principal definitions:
--   - `conicSeparatorConstraintFunctional`: the constraint-coordinate functional obtained by restricting a product-space separator.
--   - `conicSeparatorObjectiveCoefficient`: the coefficient of the objective coordinate in that separator.
--   - `conicSeparator_decompose`: decomposition of a separator into constraint contribution plus objective coefficient times the objective coordinate.
--   - `conicSeparatorObjectiveCoefficient_neg_of_above`: negativity of the objective coefficient when the separator separates a larger objective value above a conic point.
--   - `conicNormalizedSeparatorFunctional`: normalization of the constraint functional by the negative objective coefficient.
--   - `conicFunctionalDualFeasible_normalizedSeparator`: feasibility of the normalized functional for the conic functional dual inequalities.
--   - `conicNormalizedSeparatorFunctional_lt_of_sep`: strict upper bound on the normalized functional at a point where the separator is negative.
--   - `conic_primalValue_eq_dualValue_of_fiber_max_dual_min`: equality of attained primal and dual values from fiberwise primal maximality, dual minimality, and weak duality.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/Quantum/FiniteConicDuality.lean#L30-L234

-- Generated from MIPStarRE/Quantum/FiniteConicDuality.lean by skeleton subtraction.
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

namespace LIDT

/-!
# Finite conic-duality separation lemmas

This module contains the product-space part of the finite-dimensional conic
duality argument used by the Section 9 SDP.  A separator on a product space
`E × ℝ` decomposes into a constraint-coordinate functional and an objective
coefficient.  If the separator is nonnegative on a conic image and negative at
a point with the same constraint coordinate but larger objective coordinate,
then the objective coefficient is negative.  After normalizing by this negative
coefficient one obtains the functional dual bound.

The matrix trace-pairing representation and the paper-form SDP witness remain
in the Section 9 matrix-realization layer.

## References

- `references/ldt-paper/self_improvement.tex`
- `docs/reports/issue-2386-finite-sdp-duality-theorem-design.md`
-/

@[expose] public section

namespace MIPStarRE.Quantum

/-- The constraint-coordinate part of a separator on a product space. -/
noncomputable def conicSeparatorConstraintFunctional
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) :
    StrongDual ℝ E :=
  φ.comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- The objective-coordinate coefficient of a separator on a product space. -/
noncomputable def conicSeparatorObjectiveCoefficient
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) : ℝ :=
  (φ.comp (ContinuousLinearMap.inr ℝ E ℝ)) (1 : ℝ)

/-- A separator on `E × ℝ` is the sum of its constraint-coordinate part and
objective-coordinate part. -/
theorem conicSeparator_decompose
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) (y : E) (t : ℝ) :
    φ (y, t) =
      conicSeparatorConstraintFunctional φ y +
        t * conicSeparatorObjectiveCoefficient φ := by
  rw [← ContinuousLinearMap.comp_inl_add_comp_inr φ (y, t)]
  simp only [conicSeparatorConstraintFunctional, conicSeparatorObjectiveCoefficient]
  congr 1
  simpa using
    ((φ.comp (ContinuousLinearMap.inr ℝ E ℝ)).map_smul t (1 : ℝ))

/-- If a separator is nonnegative on a conic image point `(y, s)` and negative
at `(y, t)` with `s < t`, then its objective-coordinate coefficient is
negative. -/
theorem conicSeparatorObjectiveCoefficient_neg_of_above
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {C : Set (E × ℝ)}
    (φ : StrongDual ℝ (E × ℝ))
    {y : E} {s t : ℝ}
    (hφ : ∀ z ∈ C, 0 ≤ φ z)
    (hys : (y, s) ∈ C)
    (hyt : φ (y, t) < 0)
    (hst : s < t) :
    conicSeparatorObjectiveCoefficient φ < 0 := by
  have hs_nonneg :
      0 ≤
        conicSeparatorConstraintFunctional φ y +
          s * conicSeparatorObjectiveCoefficient φ := by
    have hnonneg := hφ (y, s) hys
    rwa [conicSeparator_decompose] at hnonneg
  have ht_neg :
      conicSeparatorConstraintFunctional φ y +
          t * conicSeparatorObjectiveCoefficient φ < 0 := by
    rwa [conicSeparator_decompose] at hyt
  by_contra hnot
  have hcoeff_nonneg : 0 ≤ conicSeparatorObjectiveCoefficient φ :=
    le_of_not_gt hnot
  have hmul :
      s * conicSeparatorObjectiveCoefficient φ ≤
        t * conicSeparatorObjectiveCoefficient φ :=
    mul_le_mul_of_nonneg_right (le_of_lt hst) hcoeff_nonneg
  nlinarith

/-- The normalized constraint-coordinate functional associated to a separator.

This definition is useful when the objective-coordinate coefficient is known to
be negative. -/
noncomputable def conicNormalizedSeparatorFunctional
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) :
    StrongDual ℝ E :=
  ((-conicSeparatorObjectiveCoefficient φ)⁻¹) •
    conicSeparatorConstraintFunctional φ

@[simp]
theorem conicNormalizedSeparatorFunctional_apply
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) (y : E) :
    conicNormalizedSeparatorFunctional φ y =
      ((-conicSeparatorObjectiveCoefficient φ)⁻¹) *
        conicSeparatorConstraintFunctional φ y := by
  rfl



/-- The normalized constraint functional associated to a separator is feasible
for the functional dual problem of the conic image. -/
theorem conicFunctionalDualFeasible_normalizedSeparator
    {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]
    {C : Set (F × ℝ)}
    (φ : StrongDual ℝ (F × ℝ))
    (hφ : ∀ z ∈ C, 0 ≤ φ z)
    (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
    ∀ z ∈ C, z.2 ≤ conicNormalizedSeparatorFunctional φ z.1 := by
  rintro ⟨y, t⟩ hyt
  have hpositiveCoeff : 0 < -conicSeparatorObjectiveCoefficient φ :=
    neg_pos.mpr hcoeff
  have hnonneg := hφ (y, t) hyt
  have hdecomp :
      0 ≤ conicSeparatorConstraintFunctional φ y +
        t * conicSeparatorObjectiveCoefficient φ := by
    rwa [conicSeparator_decompose] at hnonneg
  have hmul :
      t * (-conicSeparatorObjectiveCoefficient φ) ≤
        conicSeparatorConstraintFunctional φ y := by
    nlinarith
  rw [conicNormalizedSeparatorFunctional_apply]
  exact (le_inv_mul_iff₀' hpositiveCoeff).mpr hmul

/-- If a separator is negative at `(y, t)`, then its normalized
constraint-coordinate functional is below `t` at `y`. -/
theorem conicNormalizedSeparatorFunctional_lt_of_sep
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ))
    {y : E} {t : ℝ}
    (hsep : φ (y, t) < 0)
    (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
    conicNormalizedSeparatorFunctional φ y < t := by
  have hpositiveCoeff : 0 < -conicSeparatorObjectiveCoefficient φ :=
    neg_pos.mpr hcoeff
  have hsepDecomposed :
      conicSeparatorConstraintFunctional φ y +
          t * conicSeparatorObjectiveCoefficient φ < 0 := by
    rwa [conicSeparator_decompose] at hsep
  have hlt :
      conicSeparatorConstraintFunctional φ y <
        t * (-conicSeparatorObjectiveCoefficient φ) := by
    nlinarith
  rw [conicNormalizedSeparatorFunctional_apply]
  exact (inv_mul_lt_iff₀ hpositiveCoeff).mpr (by simpa [mul_comm] using hlt)

/-- A functional conic zero-gap theorem.

Let `C` be a closed conic image in `F × ℝ`.  Suppose that, on the fiber over
`y`, the value `p` lies in `C` and is maximal among all objective coordinates
in that fiber.  Suppose also that `d` is minimal among all continuous
real-linear functionals `ψ` satisfying the functional dual inequalities
`t ≤ ψ y'` for every `(y', t) ∈ C`.  If weak duality gives `p ≤ d`, then the
attained primal and dual values are equal.

This is the product-space separation argument behind finite-dimensional conic
duality.  It deliberately records the closed-image fiber condition through the
maximality hypothesis, rather than assuming that fiber recovery is automatic. -/
theorem conic_primalValue_eq_dualValue_of_fiber_max_dual_min
    {F : Type*}
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (C : ProperCone ℝ (F × ℝ))
    {y : F} {p d : ℝ}
    (hprimalMem : (y, p) ∈ C)
    (hprimalMax : ∀ {t : ℝ}, (y, t) ∈ C → t ≤ p)
    (hdualMin : ∀ ψ : StrongDual ℝ F,
      (∀ z ∈ C, z.2 ≤ ψ z.1) → d ≤ ψ y)
    (hweak : p ≤ d) :
    p = d := by
  have hd_le_p : d ≤ p := by
    by_contra hnot
    have hp_lt_d : p < d := lt_of_not_ge hnot
    let t : ℝ := (p + d) / 2
    have hp_lt_t : p < t := by
      dsimp [t]
      nlinarith
    have ht_lt_d : t < d := by
      dsimp [t]
      nlinarith
    have hnotMem : (y, t) ∉ C := by
      intro hyt
      exact (not_lt_of_ge (hprimalMax hyt)) hp_lt_t
    obtain ⟨φ, hφ_nonneg, hsep⟩ := C.hyperplane_separation_point hnotMem
    have hcoeff : conicSeparatorObjectiveCoefficient φ < 0 :=
      conicSeparatorObjectiveCoefficient_neg_of_above
        (C := (C : Set (F × ℝ))) φ hφ_nonneg hprimalMem hsep hp_lt_t
    let ψ : StrongDual ℝ F := conicNormalizedSeparatorFunctional φ
    have hψfeasible : ∀ z ∈ C, z.2 ≤ ψ z.1 := by
      simpa [ψ] using
        conicFunctionalDualFeasible_normalizedSeparator
          (C := (C : Set (F × ℝ))) φ hφ_nonneg hcoeff
    have hd_le_ψ : d ≤ ψ y := hdualMin ψ hψfeasible
    have hψ_lt_t : ψ y < t :=
      conicNormalizedSeparatorFunctional_lt_of_sep φ hsep hcoeff
    nlinarith
  exact le_antisymm hweak hd_le_p

end MIPStarRE.Quantum

end

end LIDT


