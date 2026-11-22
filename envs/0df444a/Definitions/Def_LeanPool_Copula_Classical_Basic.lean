-- Prove2me | Definitions.Def_LeanPool_Copula_Classical_Basic
-- name    : LeanPool_Copula_Classical_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:50:33.525587+00:00
-- url     : https://prove2.me/theorems/6e583fd6-14a8-4b1b-b097-bb2a5d92cc35
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Basic.lean

module
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Definitions.Def_LeanPool_Copula_Unique
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_independence
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_independence
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_comonotonic
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_independence
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.corner_empty
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.partialIncrement_empty
attribute [local simp] ProbabilityTheory.Copula.toMeasure_comonotonic
attribute [local simp] ProbabilityTheory.Copula.toMeasure_independence
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap


set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval
namespace ProbabilityTheory.Copula
variable {d : ℕ}
structure IsClassical (F : (Fin d → I) → ℝ) : Prop where
  /-- The top corner has mass one, including in dimension zero. -/
  normalized : F (fun _ => 1) = 1
  /-- A zero coordinate makes the function vanish. -/
  grounded : ∀ (u : Fin d → I) (i : Fin d), u i = 0 → F u = 0
  /-- The one-coordinate boundary faces are uniform. -/
  marginal : ∀ (i : Fin d) (u : I), F (Function.update (fun _ => 1) i u) = (u : ℝ)
  /-- Every ordered rectangle has a nonnegative increment. -/
  increasing : ∀ a b, a ≤ b → 0 ≤ rectangleIncrement F a b
@[expose]
noncomputable def IsClassical.ofMeasure {F : (Fin d → I) → ℝ} (hF : IsClassical F)
    (μ : ProbabilityMeasure (Fin d → I)) (hμ : ∀ u, μ.toMeasure.real (Iic u) = F u) : Copula d where
  measure := μ
  marginal_eq i := by
    apply Measure.ext_of_Iic
    intro t
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (μ.toMeasure.map (fun x => x i)).real (Iic t) = volume.real (Iic t)
    rw [map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic]
    have he : (fun x : Fin d → I => x i) ⁻¹' Iic t =
        Iic (Function.update (fun _ => 1) i t) := by
      ext x
      constructor
      · intro hx j
        by_cases hji : j = i
        · subst j; simpa using hx
        · simpa [Function.update_of_ne hji] using (unitInterval.le_one' (t := x j))
      · intro hx
        simpa using hx i
    rw [he, hμ, hF.marginal]
    simp [Measure.real, t.property.1]
end ProbabilityTheory.Copula


