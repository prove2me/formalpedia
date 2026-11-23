-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
-- name    : GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:37.97355+00:00
-- url     : https://prove2.me/theorems/9aae890c-2881-43ce-9ae0-a67ab36b75bf
-- title:
--   Integrated
-- statement:
--   Definitions and structural lemmas for Integrated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace UnitaryRep
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
lemma aestronglyMeasurable_inner_orbit (w v : H) :
    AEStronglyMeasurable (fun g => ⟪w, π g v⟫_ℂ) μ :=
  (continuous_const.inner (π.continuous_orbit v)).aestronglyMeasurable
omit [MeasurableSpace G] [OpensMeasurableSpace G] in
lemma norm_inner_orbit_le (w v : H) (g : G) : ‖⟪w, π g v⟫_ℂ‖ ≤ ‖w‖ * ‖v‖ := by
  calc ‖⟪w, π g v⟫_ℂ‖ ≤ ‖w‖ * ‖π g v‖ := norm_inner_le_norm _ _
    _ = ‖w‖ * ‖v‖ := by rw [norm_map]
lemma integrable_mul_inner_orbit (f : G →₁[μ] ℂ) (w v : H) :
    Integrable (fun g => f g * ⟪w, π g v⟫_ℂ) μ :=
  (L1.integrable_coeFn f).mul_bdd (π.aestronglyMeasurable_inner_orbit μ w v)
    (Eventually.of_forall fun g => π.norm_inner_orbit_le w v g)
omit [OpensMeasurableSpace G] in
lemma norm_integral_mul_inner_orbit_le (f : G →₁[μ] ℂ) (w v : H) :
    ‖∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ‖ ≤ ‖f‖ * ‖w‖ * ‖v‖ := by
  calc ‖∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ‖ ≤ ∫ g, ‖f g‖ * (‖w‖ * ‖v‖) ∂μ :=
        norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.mul_const _)
          (Eventually.of_forall fun g => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (π.norm_inner_orbit_le w v g) (norm_nonneg _))
    _ = ‖f‖ * ‖w‖ * ‖v‖ := by rw [integral_mul_const, L1.norm_eq_integral_norm, mul_assoc]
noncomputable def integratedForm (f : G →₁[μ] ℂ) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun w v => ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ)
      (fun w₁ w₂ v => by
        simp only [inner_add_left, mul_add]
        exact integral_add (π.integrable_mul_inner_orbit μ f w₁ v)
          (π.integrable_mul_inner_orbit μ f w₂ v))
      (fun c w v => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; ring)
      (fun w v₁ v₂ => by
        simp only [map_add, inner_add_right, mul_add]
        exact integral_add (π.integrable_mul_inner_orbit μ f w v₁)
          (π.integrable_mul_inner_orbit μ f w v₂))
      (fun c w v => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; ext g; ring))
    ‖f‖ (fun w v => π.norm_integral_mul_inner_orbit_le μ f w v)
noncomputable def integratedOp (f : G →₁[μ] ℂ) : H →L[ℂ] H :=
  adjoint (InnerProductSpace.continuousLinearMapOfBilin (π.integratedForm μ f))
lemma inner_integratedOp (f : G →₁[μ] ℂ) (w v : H) :
    ⟪w, π.integratedOp μ f v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  rw [integratedOp, adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl
lemma norm_integratedOp_apply_le (f : G →₁[μ] ℂ) (v : H) :
    ‖π.integratedOp μ f v‖ ≤ ‖f‖ * ‖v‖ := by
  set x := π.integratedOp μ f v
  have h := π.norm_integral_mul_inner_orbit_le μ f x v
  rw [← inner_integratedOp] at h
  have h' : ‖x‖ * ‖x‖ ≤ ‖x‖ * (‖f‖ * ‖v‖) := by
    have e : ‖⟪x, x⟫_ℂ‖ = ‖x‖ * ‖x‖ := by rw [inner_self_eq_norm_sq_to_K]; simp [sq]
    rw [e] at h
    linarith
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_left h' hpos
noncomputable def integrated : (G →₁[μ] ℂ) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := π.integratedOp μ
      map_add' := fun f₁ f₂ => by
        refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
        rw [add_apply, inner_add_right, inner_integratedOp, inner_integratedOp,
          inner_integratedOp, ← integral_add (π.integrable_mul_inner_orbit μ f₁ w v)
            (π.integrable_mul_inner_orbit μ f₂ w v)]
        refine integral_congr_ae ((Lp.coeFn_add f₁ f₂).mono fun g hg => ?_)
        simp only [hg, Pi.add_apply, add_mul]
      map_smul' := fun c f => by
        refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
        rw [smul_apply, inner_smul_right, inner_integratedOp, inner_integratedOp,
          RingHom.id_apply, ← integral_const_mul]
        refine integral_congr_ae ((Lp.coeFn_smul c f).mono fun g hg => ?_)
        simp only [hg, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    1 (fun f => by
      rw [one_mul]
      exact opNorm_le_bound _ (norm_nonneg _) fun v => π.norm_integratedOp_apply_le μ f v)
section translate
variable [IsTopologicalGroup G] [BorelSpace G]
noncomputable def leftTranslate [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) : G →₁[μ] ℂ :=
  Lp.compMeasurePreserving (fun g => h⁻¹ * g) (measurePreserving_mul_left μ h⁻¹) f
noncomputable def involution [μ.IsInvInvariant] (f : G →₁[μ] ℂ) : G →₁[μ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp
    (Lp.compMeasurePreserving (fun g => g⁻¹) (Measure.measurePreserving_inv μ) f)
end translate
end UnitaryRep
end GroundTheory.Automorphic


