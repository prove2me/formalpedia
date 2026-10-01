-- Prove2me | Definitions.Def_ChapterQuantumGravityHalfDensity
-- name    : ChapterQuantumGravityHalfDensity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:33:48.25767+00:00
-- url     : https://prove2.me/theorems/757ab7d7-a8bf-4ff4-8dd6-99f586b6dd4b
-- title:
--   Chapter QuantumGravityHalfDensity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuantumGravityHalfDensity.lean`): generated def bundle for ChapterQuantumGravityHalfDensity. See BookProof/ChapterQuantumGravityHalfDensity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityHalfDensity.lean

import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib


/-!
# Quantum gravity: the half-density unitary of the densitized change of variables

This module closes the one piece of `PLAN_LEAN_SPECIALIST_QG_FLOW.md` Part D that
was previously left as *data*: the plan's honest boundary records that

> the raw point map `e ↦ (y, ẽ)` is not by itself a Hilbert-space unitary; the
> Jacobian half-density factor `|J|^{−1/2}` is what makes D.4 applicable.  The
> transfer theorem takes that unitary as data.

Here the unitary is **constructed**, not assumed.

## The construction

On the conformal factor alone the densitized change of variables is
`e = y²` (equivalently `y = √e`), a diffeomorphism of `(0, ∞)`.  Its Jacobian is
`de/dy = 2y`, so the half-density factor is `√(2y)` and the correct statement is
that composition with `y ↦ y²` is a **unitary**

  `L²((0,∞), de)  ≃  L²((0,∞), 2y dy)`,

the second space being `L²` of the *half-density weighted* measure
`qgSrcMeasure = (2y dy)|_{(0,∞)}`, whose density is exactly the square
`(√(2y))²` of the half-density factor.

## Main results

* `measurePreserving_qgSquare`, `measurePreserving_qgSqrt` — the change of
  variables `y ↦ y²` is measure preserving from the weighted measure `2y dy` to
  Lebesgue measure on `(0, ∞)`, and `√·` is measure preserving the other way;
* `qgSrcMeasure_density_eq_halfDensity_sq` — the weight `2y` is the *square* of
  the Jacobian half-density factor `√(2y)`;
* `halfDensityUnitary` — the resulting unitary
  `L²((0,∞), de) ≃ₗᵢ[ℂ] L²((0,∞), 2y dy)`, together with the pointwise formula
  `halfDensityUnitary_apply` (`(W g)(y) = g(y²)` a.e.) and the norm identity
  `halfDensityUnitary_norm`;
* `qg_halfDensity_transfer` — the Part D.4 transfer theorem
  `BookProof.QuantumGravityDensitized.densitized_hasZeroDeficiencyOn_transfer`
  instantiated **at this concrete unitary**, so that the transfer hypothesis
  "there is a half-density unitary intertwining the two Hamiltonians" is shown
  to be about a genuinely existing map;
* `exists_halfDensity_unitary` — the bare existence statement.

## Scope

Nothing here claims essential self-adjointness of the continuum gravity
operator.  What is added is exactly the missing constructive ingredient of the
transfer step: the half-density unitary itself.
-/

namespace BookProof.QuantumGravityHalfDensity

open MeasureTheory Set Filter
open scoped ENNReal

/-! ## The half-density factor and the weighted measure -/

/-- The Jacobian of the conformal change of variables `e = y²`, i.e. `de/dy`. -/
def qgJacobian (y : ℝ) : ℝ := 2 * y

/-- The **half-density factor** `|J|^{1/2} = √(2y)` of the change of variables. -/
noncomputable def qgHalfDensity (y : ℝ) : ℝ := Real.sqrt (qgJacobian y)

/-- The weighted ("half-density") measure `2y dy` on `(0, ∞)`. -/
noncomputable def qgSrcMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun y => ENNReal.ofReal (qgJacobian y)





/-- `qgSrcMeasure` lives on `(0, ∞)`. -/
theorem qgSrcMeasure_ae_pos : ∀ᵐ y ∂qgSrcMeasure, 0 < y :=
  (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Ioi)

/-! ## The change of variables `e = y²` is measure preserving -/

/-- The conformal point map `y ↦ y² = e`. -/
def qgSquare (y : ℝ) : ℝ := y ^ 2

theorem measurable_qgSquare : Measurable qgSquare := by
  unfold qgSquare; fun_prop

theorem measurable_qgSqrt : Measurable Real.sqrt := Real.continuous_sqrt.measurable

/-- `y ↦ y²` maps `{y > 0 : y² ∈ A}` onto `A ∩ (0, ∞)`. -/
theorem qgSquare_image (A : Set ℝ) :
    qgSquare '' (qgSquare ⁻¹' A ∩ Set.Ioi 0) = A ∩ Set.Ioi 0 := by
  ext e
  constructor
  · rintro ⟨y, ⟨hyA, hy0⟩, rfl⟩
    exact ⟨hyA, by simpa [qgSquare] using pow_pos hy0 2⟩
  · rintro ⟨heA, he0⟩
    refine ⟨Real.sqrt e, ⟨?_, Real.sqrt_pos.mpr he0⟩, ?_⟩
    · simpa [qgSquare, Real.sq_sqrt he0.le] using heA
    · simpa [qgSquare] using Real.sq_sqrt he0.le

/-- **The densitized change of variables is measure preserving.**  Pushing the
half-density measure `2y dy` forward along `y ↦ y²` gives Lebesgue measure `de`
on `(0, ∞)`.  This is the precise content of the Jacobian factor. -/
theorem measurePreserving_qgSquare :
    MeasurePreserving qgSquare qgSrcMeasure (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨measurable_qgSquare, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_qgSquare hA]
  have hpm : MeasurableSet (qgSquare ⁻¹' A) := hA.preimage measurable_qgSquare
  set s := qgSquare ⁻¹' A ∩ Set.Ioi (0 : ℝ) with hs
  have hsm : MeasurableSet s := hpm.inter measurableSet_Ioi
  have hkey : ∫⁻ x in qgSquare '' s, (1 : ℝ≥0∞) = ∫⁻ y in s, ENNReal.ofReal (|2 * y|) * 1 := by
    refine MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul hsm ?_ ?_ _
    · intro x _
      exact ((hasDerivAt_pow 2 x).hasDerivWithinAt (s := s)).congr_deriv (by ring)
    · intro a ha b hb hab
      have ha0 : (0 : ℝ) < a := ha.2
      have hb0 : (0 : ℝ) < b := hb.2
      have hsq : a ^ 2 = b ^ 2 := hab
      nlinarith
  rw [qgSquare_image A] at hkey
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at hkey
  have hR : qgSrcMeasure (qgSquare ⁻¹' A) = ∫⁻ y in s, ENNReal.ofReal (2 * y) := by
    rw [qgSrcMeasure, withDensity_apply _ hpm, Measure.restrict_restrict hpm, hs, Set.inter_comm]
    rfl
  have habs : ∫⁻ y in s, ENNReal.ofReal (|2 * y|) = ∫⁻ y in s, ENNReal.ofReal (2 * y) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hsm] with y hy
    have hy0 : (0 : ℝ) < y := hy.2
    rw [abs_of_nonneg (by linarith)]
  rw [hR, ← habs, ← hkey, Measure.restrict_apply hA]

/-- The inverse change of variables `e ↦ √e` is measure preserving the other
way. -/
theorem measurePreserving_qgSqrt :
    MeasurePreserving Real.sqrt (volume.restrict (Set.Ioi (0 : ℝ))) qgSrcMeasure := by
  refine ⟨measurable_qgSqrt, ?_⟩
  rw [← measurePreserving_qgSquare.map_eq, Measure.map_map measurable_qgSqrt measurable_qgSquare]
  have h : (Real.sqrt ∘ qgSquare) =ᵐ[qgSrcMeasure] id := by
    filter_upwards [qgSrcMeasure_ae_pos] with y hy
    simp [qgSquare, Real.sqrt_sq hy.le]
  rw [Measure.map_congr h, Measure.map_id]

/-! ## The half-density unitary -/

/-- Composition with the point map, as a linear isometry
`L²((0,∞), de) →ₗᵢ L²((0,∞), 2y dy)`. -/
noncomputable def halfDensityIsom :
    Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ))) →ₗᵢ[ℂ] Lp ℂ 2 qgSrcMeasure :=
  Lp.compMeasurePreservingₗᵢ ℂ qgSquare measurePreserving_qgSquare

/-- Composition with the inverse point map, the candidate inverse isometry. -/
noncomputable def halfDensityIsomInv :
    Lp ℂ 2 qgSrcMeasure →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  Lp.compMeasurePreservingₗᵢ ℂ Real.sqrt measurePreserving_qgSqrt

theorem halfDensityIsom_halfDensityIsomInv (h : Lp ℂ 2 qgSrcMeasure) :
    halfDensityIsom (halfDensityIsomInv h) = h := by
  refine Lp.ext ?_
  have h1 : (halfDensityIsom (halfDensityIsomInv h) : ℝ → ℂ)
      =ᵐ[qgSrcMeasure] fun y => (halfDensityIsomInv h : ℝ → ℂ) (qgSquare y) :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_qgSquare
  have h2 : (halfDensityIsomInv h : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun e => (h : ℝ → ℂ) (Real.sqrt e) :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_qgSqrt
  have h3 := h2.comp_tendsto measurePreserving_qgSquare.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, h3, qgSrcMeasure_ae_pos] with y hy1 hy3 hy0
  rw [hy1]
  simp only [Function.comp_apply] at hy3
  rw [hy3]
  simp [qgSquare, Real.sqrt_sq hy0.le]

theorem halfDensityIsom_surjective : Function.Surjective halfDensityIsom :=
  fun h => ⟨halfDensityIsomInv h, halfDensityIsom_halfDensityIsomInv h⟩

/-- **The half-density unitary.**  The densitized change of variables `e = y²`,
paired with the Jacobian half-density weight `2y = (√(2y))²`, is a genuine
Hilbert-space unitary

  `L²((0,∞), de)  ≃ₗᵢ[ℂ]  L²((0,∞), 2y dy)`.

This is the map that Part D.4 of the plan previously had to take as data. -/
noncomputable def halfDensityUnitary :
    Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2 qgSrcMeasure :=
  LinearIsometryEquiv.ofSurjective halfDensityIsom halfDensityIsom_surjective









/-! ## The Part D.4 transfer, instantiated at the constructed unitary -/

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LagrangianEsa



end BookProof.QuantumGravityHalfDensity


