-- Prove2me | Definitions.Def_LeanPool_Copula_Sklar_Continuous
-- name    : LeanPool_Copula_Sklar_Continuous
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:44:07.444649+00:00
-- url     : https://prove2.me/theorems/bbb7058f-8663-4e07-8f61-87bb9c5c4e11
-- title:
--   Continuous
-- statement:
--   Definitions and structural lemmas for Continuous, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/Continuous.lean

module
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_CDF
public import Theorems.Thm_ProbabilityTheory_map_cdfUnit
public import Theorems.Thm_ProbabilityTheory_measurable_cdfUnit
attribute [local fun_prop] ProbabilityTheory.measurable_cdfUnit


set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set Filter
open scoped unitInterval
namespace ProbabilityTheory.Copula
variable {d : ℕ}
@[expose]
noncomputable def marginal (μ : ProbabilityMeasure (Fin d → ℝ)) (i : Fin d) : Measure ℝ :=
  μ.toMeasure.map (fun x => x i)
instance (μ : ProbabilityMeasure (Fin d → ℝ)) (i : Fin d) : IsProbabilityMeasure (marginal μ i) :=
  by
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
@[expose]
noncomputable def marginalTransform (μ : ProbabilityMeasure (Fin d → ℝ)) (x : Fin d → ℝ)
    (i : Fin d) : I := cdfUnit (marginal μ i) (x i)
theorem measurable_marginalTransform (μ : ProbabilityMeasure (Fin d → ℝ)) :
    Measurable (marginalTransform μ) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_cdfUnit (marginal μ i)).comp (measurable_pi_apply i)
theorem map_marginalTransform_eval (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) (i : Fin d) :
    μ.toMeasure.map (fun x => marginalTransform μ x i) = volume := by
  calc
    _ = (marginal μ i).map (cdfUnit (marginal μ i)) :=
      (Measure.map_map (measurable_cdfUnit _) (measurable_pi_apply i)).symm
    _ = volume := map_cdfUnit _ (hc i)
@[expose]
noncomputable def ofContinuousMarginals (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) : Copula d :=
  ofMap μ (marginalTransform μ) (measurable_marginalTransform μ)
    (map_marginalTransform_eval μ hc)
@[expose]
def IsSklarCopula (μ : ProbabilityMeasure (Fin d → ℝ)) (C : Copula d) : Prop :=
  ∀ x, C.cdf (marginalTransform μ x) = μ.toMeasure.real (Iic x)
end ProbabilityTheory.Copula


