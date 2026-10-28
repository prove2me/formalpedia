-- Prove2me | Definitions.Def_OAIQ6El005
-- name    : OAIQ6El005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:23:20.449368+00:00
-- url     : https://prove2.me/theorems/9a707fe0-1405-402d-afd7-72bbcbba950d
-- title:
--   Definitions bundle OAIQ6El005 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 39 definitions, 1 instance and 4 theorems. The definitions and types are `OAI.ElasticityDistribution.finiteResidual`, `OAI.ElasticityDistribution.normald`, `OAI.ElasticityDistribution.planeDerivative`, `OAI.ElasticityFiniteType.C`, `OAI.ElasticityFrame.scalarSmooth`, `OAI.ElasticityFrame.smoothProjection`, `OAI.ElasticityFrame.vectorSmooth`, `OAI.ElasticityODE.evolution`, `OAI.ElasticityODE.flow`, `OAI.ElasticityODE.frameDbar`, `OAI.ElasticityODE.fundamental`, `OAI.ElasticityODE.integrate`, `OAI.ElasticityODE.integrateCLM`, `OAI.ElasticityODE.leftCoeff`, `OAI.ElasticityODE.leftCoeffCLM`, `OAI.ElasticityODE.reciprocal`, `OAI.ElasticityODE.rightCoeff`, `OAI.ElasticityODE.weightedCLM`, `OAI.ElasticityPhysicalEstimate.X`, `OAI.ElasticityPhysicalEstimate.aPhys`, `OAI.ElasticityPhysicalEstimate.cPhys`, `OAI.ElasticityPhysicalEstimate.vPhys`, `OAI.ElasticityPhysicalSolvability.X`, `OAI.ElasticityPlanar.B`, `OAI.ElasticityPlanar.C`, `OAI.ElasticityPlanar.GraphSpace`, `OAI.ElasticityPlanar.adjTransport`, `OAI.ElasticityPlanar.closedGraph`, `OAI.ElasticityPlanar.entryInjection`, `OAI.ElasticityPlanar.graphFirst`, `OAI.ElasticityPlanar.graphSecond`, `OAI.ElasticityPlanar.mass`, `OAI.ElasticityPlanar.pair`, `OAI.ElasticityPlanar.planarOperator`, `OAI.ElasticityPlanar.supported`, `OAI.ElasticityPlanar.testGraph`, `OAI.ElasticityPlanar.transport`, `OAI.ElasticityRegularity.SmoothLocalSobolev`, `OAI.ElasticityRegularity.SmoothSobolev`.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: [`Elasticity_CGO`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean), [`Elasticity_Carleman`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Carleman.lean), [`Elasticity_Homotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Homotopy.lean), [`Elasticity_ODE`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/ODE.lean), [`Elasticity_Parameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Parameters.lean), [`Elasticity_Planar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Planar.lean), [`Elasticity_Recovery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Recovery.lean), [`Elasticity_Smoothing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean), [`Elasticity_Solvability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Solvability.lean), [`Elasticity_Supported`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean), [`Elasticity_Transport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean), [`Elasticity_WeakLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean).
--
--   **Imports.** It imports the bundles `OAIQ6El000`, `OAIQ6El001`, `OAIQ6El002` and `OAIQ6El003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ6El006` and `OAIQ6El007`; the statements `OAI_ElasticityAugmented_normal_form_bottom_residual_at`, `OAI_ElasticityAugmented_normal_form_forced_residual`, `OAI_ElasticityAugmented_recurs_compatible`, `OAI_ElasticityBoundaryDensityPull_density_chart_all`, `OAI_ElasticityBoundaryPacket_Setup_energy_difference_normal`, `OAI_ElasticityBoundaryPacket_Setup_field_force_mass`, `OAI_ElasticityBoundaryPacket_Setup_field_value_mass`, `OAI_ElasticityBoundaryPacket_Setup_linearCoeff_zero`, `OAI_ElasticityBoundaryResidualMass_projected_trial_residual`, `OAI_ElasticityCGO_cut_actual_augmented_bound`, `OAI.ElasticityCGO.cut_truncation_residual`, `OAI_ElasticityCGO_formal_scalar_polynomial`, `OAI_ElasticityCGO_localized_formal_divergence_H1_bound`, `OAI.ElasticityDistribution.compact_transport_smoothing`, `OAI.ElasticityODE.frameDbar_hasDerivWithinAt`, `OAI.ElasticityODE.fundamental_isUnit`, `OAI.ElasticityODE.fundamental_transport`, `OAI.ElasticityPlanar.dbar_fundamental`, `OAI.ElasticityPlanar.global_supported_of_dense`, `OAI.ElasticityPlanar.local_graph_solution`, `OAI.ElasticityPlanar.local_supported_of_dense_tests`, `OAI.ElasticityPlanar.supported_parameter_inversion`, `OAI.ElasticityPlanar.supported_smooth_test_family`, `OAI.ElasticityPlanar.supported_weak_unique`, `OAI_Elasticity_dn_common_leading_frame` and `OAI_Elasticity_extended_dn_compact_comparison`; the proofs of `OAI.ElasticityAugmented.exists_physical_forced_transport`, `OAI.ElasticityAugmented.exists_physical_leading_frame`, `OAI_ElasticityAugmented_normal_form_bottom_residual_at`, `OAI_ElasticityAugmented_normal_form_forced_residual`, `OAI_ElasticityAugmented_recurs_compatible`, `OAI.ElasticityAugmented.supported_matrix_smooth`, `OAI.ElasticityAugmented.supported_matrix_unique`, `OAI_ElasticityBoundaryDensityPull_density_chart_all`, `OAI_ElasticityBoundaryPacket_Setup_energy_difference_normal`, `OAI_ElasticityBoundaryPacket_Setup_field_force_mass`, `OAI_ElasticityBoundaryPacket_Setup_field_value_mass`, `OAI_ElasticityBoundaryPacket_Setup_linearCoeff_zero`, `OAI_ElasticityBoundaryResidualMass_projected_trial_residual`, `OAI_ElasticityCGO_cut_actual_augmented_bound`, `OAI.ElasticityCGO.cut_truncation_residual`, `OAI_ElasticityCGO_formal_scalar_polynomial`, `OAI_ElasticityCGO_localized_formal_divergence_H1_bound`, `OAI.ElasticityGeneralSlicing.smooth_cylinder_representative`, `OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder`, `OAI.ElasticityODE.frameDbar_hasDerivWithinAt`, `OAI.ElasticityODE.fundamental_isUnit`, `OAI.ElasticityODE.fundamental_transport`, `OAI.ElasticityParameter.holomorphic_of_supported_transport`, `OAI.ElasticityPlanar.dbar_fundamental`, `OAI.ElasticityPlanar.exists_algebra_variable_homotopy`, `OAI.ElasticityPlanar.exists_spatial_transport`, `OAI.ElasticityPlanar.global_supported_of_dense`, `OAI.ElasticityPlanar.local_graph_solution`, `OAI.ElasticityPlanar.local_supported_of_dense_tests`, `OAI.ElasticityPlanar.spatial_frame_of_left_inverse`, `OAI.ElasticityPlanar.supported_parameter_inversion`, `OAI.ElasticityPlanar.supported_smooth_test_family`, `OAI.ElasticityPlanar.supported_weak_unique` and `OAI_Elasticity_physical_supported_transfer`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003

section
-- module Solutions.OAIQ6_Elast.Elasticity_ODE
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma weighted_bound (k : ℝ) (hk : 0<k) (f : C(Time,F)) : ‖weighted k f‖ ≤ k⁻¹*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (inv_nonneg.mpr hk.le) (norm_nonneg f))).mpr
  intro t
  change ‖Real.exp (-k*(t:ℝ)) • ∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hb : ‖∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s‖ ≤
      ∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s)*‖f‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
    · exact Filter.Eventually.of_forall (fun s _ => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (extend_norm_le f s) (Real.exp_pos _).le)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_const,integral_exp_mul k _ hk.ne'] at hb
  calc
    _ ≤ Real.exp (-k*(t:ℝ))*(((Real.exp (k*(t:ℝ))-1)/k)*‖f‖) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ((1-Real.exp (-k*(t:ℝ)))/k)*‖f‖ := by
      have he : Real.exp (-k*(t:ℝ))*Real.exp (k*(t:ℝ))=1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc
        _ = (Real.exp (-k*(t:ℝ))*(Real.exp (k*(t:ℝ))-1))/k*‖f‖ := by ring
        _ = _ := by rw [mul_sub,he,mul_one]
    _ ≤ k⁻¹*‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-k*(t:ℝ))]) hk.le

/-- The actual exponentially weighted integration operator on the time interval.
Its norm is at most 1/k; this supplies a uniform contraction for arbitrary bounded
linear ODE coefficients, without an assumed global flow theorem. -/
def weightedCLM (k : ℝ) (hk : 0<k) : C(Time,F) →L[ℝ] C(Time,F) :=
  LinearMap.mkContinuous
    ({ toFun := weighted k
       map_add' := fun f g => by
         ext t
         change Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • (extend f s+extend g s)) =
           Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s)+
           Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend g s)
         have hc (v : C(Time,F)) : Continuous (fun s : ℝ => Real.exp (k*s) • extend v s) :=
           (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (extend v).continuous
         simp_rw [smul_add]
         rw [intervalIntegral.integral_add ((hc f).intervalIntegrable _ _) ((hc g).intervalIntegrable _ _),smul_add]
       map_smul' := fun c f => by
         ext t
         change Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • (c • extend f s)) =
           c • (Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s))
         simp_rw [smul_comm (Real.exp (k*_)) c]
         rw [intervalIntegral.integral_smul,smul_comm]
 } : C(Time,F) →ₗ[ℝ] C(Time,F))
    k⁻¹ (fun f => weighted_bound k hk f)

end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual continuous evolution, defined by the invertible weighted Volterra
operator. The coefficient need only be continuous in time. -/
def evolution (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F)) (y : F) : C(Time,F) :=
  expScale k ((Ring.inverse ((1 : C(Time,F) →L[ℝ] C(Time,F))-weightedCLM k hk*pointwiseCLM b) : C(Time,F) →L[ℝ] C(Time,F))
    (expScale (-k) (ContinuousMap.const Time y)))

end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A globally defined linear evolution, not restricted to small coefficients. -/
def flow (b : C(Time,F →L[ℝ] F)) (y : F) : C(Time,F) :=
  evolution (‖b‖+1) (by positivity) b y
end ElasticityODE

end
end
section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
def leftCoeff (b : C(Time,R)) : C(Time,R →L[ℝ] R) :=
  ⟨fun t => ContinuousLinearMap.mul ℝ R (b t),
    (ContinuousLinearMap.mul ℝ R).continuous.comp b.continuous⟩
def rightCoeff (b : C(Time,R)) : C(Time,R →L[ℝ] R) :=
  ⟨fun t => (ContinuousLinearMap.mul ℝ R).flip (b t),
    (ContinuousLinearMap.mul ℝ R).flip.continuous.comp b.continuous⟩
def fundamental (b : C(Time,R)) : C(Time,R) := flow (leftCoeff b) 1
def reciprocal (b : C(Time,R)) : C(Time,R) := flow (-rightCoeff b) 1
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
def integrate (f : C(Time,F)) : C(Time,F) :=
  ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), extend f s,
    (intervalIntegral.differentiable_integral_of_continuous (extend f).continuous).continuous.comp
      continuous_subtype_val⟩
lemma integrate_bound (f : C(Time,F)) : ‖integrate f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..(t:ℝ), extend f s‖ ≤ ‖f‖
  have h := intervalIntegral.norm_integral_le_of_norm_le t.property.1
    (Filter.Eventually.of_forall (fun s (_ : s ∈ Ioc (0:ℝ) (t:ℝ)) => extend_norm_le f s))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f‖) volume 0 (t:ℝ))
  calc
    _ ≤ ∫ s in (0:ℝ)..(t:ℝ), ‖f‖ := h
    _ = (t:ℝ)*‖f‖ := by simp
    _ ≤ ‖f‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg f)

def integrateCLM : C(Time,F) →L[ℝ] C(Time,F) :=
  LinearMap.mkContinuous
    ({ toFun := integrate
       map_add' := fun f g => by
         ext t
         change (∫ s in (0:ℝ)..(t:ℝ), (extend f s+extend g s)) =
           (∫ s in (0:ℝ)..(t:ℝ), extend f s)+(∫ s in (0:ℝ)..(t:ℝ), extend g s)
         exact intervalIntegral.integral_add ((extend f).continuous.intervalIntegrable _ _)
           ((extend g).continuous.intervalIntegrable _ _)
       map_smul' := fun c f => by
         ext t
         exact intervalIntegral.integral_smul c (fun s => extend f s)
    } : C(Time,F) →ₗ[ℝ] C(Time,F)) 1 (fun f => by
      change ‖integrate f‖ ≤ 1*‖f‖
      simpa only [one_mul] using integrate_bound f)
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {R P : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
def leftCoeffCLM : C(Time,R) →L[ℝ] C(Time,R →L[ℝ] R) :=
  (ContinuousLinearMap.mul ℝ R).compLeftContinuous ℝ Time
end ElasticityODE

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
abbrev X := ElasticityBessel.X

end ElasticityPhysicalEstimate

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology
namespace ElasticityPhysicalEstimate

section
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV shifted)

/-- The actual normalized matrix coefficients, with the sign of the Carleman operator. -/
def aPhys (lam m n o : Smooth) (k : Fin 3) (i j : Fin 4) : X → ℂ :=
  -((coeffA coord lam m n o k i j : Smooth) : X → ℂ)
def vPhys (lam m n o : Smooth) (i j : Fin 4) : X → ℂ :=
  -((coeffV coord lam m n o i j : Smooth) : X → ℂ)
def cPhys (m n : Smooth) (i : Fin 3) : X → ℂ := (-2*n*coord i m : Smooth)

end

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)

end ElasticityPhysicalEstimate

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalSolvability
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityAugmented
open ElasticityPhysicalDual
abbrev X := ElasticityAugmented.X

end ElasticityPhysicalSolvability

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Complex

def pair (f g : Test) : ℂ := ∫ z : ℂ, star (f z) * g z

/-- Twice dbar conjugated by exp(t|z|²/2). -/
def B (t : ℝ) : Test →ₗ[ℂ] Test := d 1 + Complex.I • d Complex.I - (t : ℂ) • Z
/-- Formal Hermitian adjoint. -/
def C (t : ℝ) : Test →ₗ[ℂ] Test := -d 1 + Complex.I • d Complex.I - (t : ℂ) • Zbar

def mass (f : Test) : ℝ := (pair f f).re

open scoped BigOperators

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators

lemma cj_add (f g : Test) : cj (f+g)=cj f+cj g := by ext z; exact star_add _ _
lemma cj_smul (c : ℂ) (f : Test) : cj (c • f)=star c • cj f := by
  apply Subtype.ext
  funext z
  change star (c*f z)=star c*star (f z)
  rw [star_mul,mul_comm]

variable {n : Type*}
variable [Fintype n]

/-- Actual first-order matrix transport on compactly supported smooth tests. -/
def transport (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    (n → Test) →ₗ[ℂ] (n → Test) where
  toFun u i := d 1 (u i)+I • d I (u i)+∑ j, mulSmooth (a i j) (ha i j) (u j)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply,map_add,Finset.sum_add_distrib,smul_add]
    abel
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply,map_smul,smul_add,Finset.smul_sum,smul_comm I c,RingHom.id_apply]

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators
variable {n : Type*} [Fintype n]

/-- The genuine Hermitian formal adjoint of dbar+a, written using conjugation
and the transpose coefficient. No elliptic right inverse is assumed. -/
def adjTransport (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    (n → Test) →ₗ[ℂ] (n → Test) where
  toFun u i := -cj (transport (fun i j z => -a j i z) (fun i j => (ha j i).neg)
    (fun j => cj (u j)) i)
  map_add' u v := by
    have hh : (fun i => cj ((u+v) i))=(fun i => cj (u i))+(fun i => cj (v i)) := by
      funext i; exact cj_add _ _
    rw [hh,map_add]
    funext i
    simp only [Pi.add_apply,cj_add,neg_add_rev,add_comm]
  map_smul' c u := by
    have hh : (fun i => cj ((c • u) i))=star c • (fun i => cj (u i)) := by
      funext i; exact cj_smul _ _
    rw [hh,map_smul]
    funext i
    simp only [Pi.smul_apply,cj_smul,star_star,smul_neg,RingHom.id_apply]

/-- Supported test vectors form the actual L2 domain for the adjoint. -/
def supported (S : Set ℂ) : Submodule ℂ (n → Test) where
  carrier := {u | ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S}
  zero_mem' _ := by simpa only [Pi.zero_apply,Submodule.coe_zero,tsupport_zero] using Set.empty_subset S
  add_mem' hu hv i := (tsupport_add _ _).trans (Set.union_subset (hu i) (hv i))
  smul_mem' c u hu i := (tsupport_smul_subset_right (fun _ : ℂ => c) (u i : ℂ → ℂ)).trans (hu i)

end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

def entryInjection (i : n) : Hilbert n →L[ℂ] 𝓢'(ℂ,ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2).comp
    ((ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap)

def planarOperator (a : n → n → ℂ → ℂ) (i : n) : Hilbert n →L[ℂ] 𝓢'(ℂ,ℂ) :=
  ((LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℂ,ℂ) (1 : ℂ))+
    Complex.I • (LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℂ,ℂ) Complex.I)).comp (entryInjection i)+
    ∑ j, (smulLeftCLM ℂ (a i j)).comp (entryInjection j)
end ElasticityPlanar
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Smooth dependence in the genuine Hilbert Sobolev topology, with the
representative tied to the given distribution family. -/
def SmoothSobolev (s : ℝ) (u : P → 𝓢'(E,ℂ)) : Prop :=
  ∃ f : P → Lp ℂ 2 (volume : Measure E), ContDiff ℝ (⊤ : ℕ∞) f ∧
    ∀ p, sobolevInjection s (f p)=u p

def SmoothLocalSobolev (Ω : Set E) (s : ℝ) (u : P → 𝓢'(E,ℂ)) : Prop :=
  ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
    SmoothSobolev s (fun p => smulLeftCLM ℂ g (u p))

end ElasticityRegularity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Homotopy
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
def frameDbar (b : ℂ → C(Time,R)) (p : ℂ) : C(Time,R) :=
  fderiv ℝ (fun p => fundamental (b p)) p 1+
    Complex.I • fderiv ℝ (fun p => fundamental (b p)) p Complex.I
end ElasticityODE

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityFrame
open scoped BigOperators
open ElasticityAugmented

def smoothProjection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] ℂ) (u : X → F) (hu : ContDiff ℝ (⊤ : ℕ∞) u) : Smooth :=
  ⟨fun x => L (u x),(L.restrictScalars ℝ).contDiff.comp hu⟩

def vectorSmooth (θ : Fin 3 → ℂ) (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Fin 3 → Smooth := fun i => smoothProjection (vectorPr θ i) u hu
def scalarSmooth (θ : Fin 3 → ℂ) (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Smooth := smoothProjection (scalarPr θ) u hu

end ElasticityFrame

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityAugmented ElasticityRegularity

/-- The two true terms in the physical residual at truncation order eight. -/
def finiteResidual (h : ℝ) (f₀ f₁ : Fin 3 → S) : Fin 3 → S :=
  (h : ℂ)^8 • f₀+(h : ℂ)^7 • f₁

end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
noncomputable section
open Set Filter Module
open scoped BigOperators Topology

namespace ElasticityFiniteType

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Closure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def C (e : ι → E) (B : ι → ι → ι → E → ℝ) (s i b : ι) (x : E) : ℝ :=
  D (B s i b) (e i) x - D (B i i b) (e s) x +
    ∑ a, (B s i a x * B a i b x - B i i a x * B a s b x)

end Closure

end ElasticityFiniteType

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented TemperedDistribution TrivSqZeroExt

def normald (θ : Fin 3 → ℂ) (u : Fin 3 → Dist) : Dist := ∑ i, θ i • u i
end
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

section
variable {n : Type*} [Fintype n]
abbrev GraphSpace (n : Type*) := WithLp 2 (Hilbert n × Hilbert n)
def testGraph (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : supported (n := n) S →ₗ[ℂ] GraphSpace n :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (Hilbert n) (Hilbert n)).symm.toLinearMap.comp
    ((embed.comp (supported S).subtype).prod
      ((embed.comp (transport a ha)).comp (supported S).subtype))
def closedGraph (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : Submodule ℂ (GraphSpace n) :=
  (testGraph S a ha).range.topologicalClosure
instance graphComplete (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : CompleteSpace (closedGraph S a ha) :=
  (testGraph S a ha).range.isClosed_topologicalClosure.completeSpace_coe

def graphFirst (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : closedGraph S a ha →L[ℂ] Hilbert n :=
  (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n)).comp (closedGraph S a ha).subtypeL
def graphSecond (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) : closedGraph S a ha →L[ℂ] Hilbert n :=
  (WithLp.sndL 2 ℂ (Hilbert n) (Hilbert n)).comp (closedGraph S a ha).subtypeL

end
open ElasticityRegularity
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv ENNReal BigOperators
open ElasticityRegularity
variable {n P : Type*} [Fintype n]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

def planeDerivative (α β : X) : Dist →L[ℂ] Dist :=
  LineDeriv.lineDerivOpCLM ℂ Dist α+Complex.I • LineDeriv.lineDerivOpCLM ℂ Dist β
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end


