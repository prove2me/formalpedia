-- Prove2me | Definitions.Def_LeanPool_Copula_Unique
-- name    : LeanPool_Copula_Unique
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:49:50.680136+00:00
-- url     : https://prove2.me/theorems/5422e787-ccbd-4451-8374-0603b9998ec0
-- title:
--   Unique
-- statement:
--   Definitions and structural lemmas for Unique, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Unique.lean

module
public import Definitions.Def_LeanPool_Copula_Independence
public import Definitions.Def_LeanPool_Copula_Comonotonic
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_independence
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_ext_cdf
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_independence
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_comonotonic
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_independence
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_comonotonic
attribute [local simp] ProbabilityTheory.Copula.toMeasure_independence
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap


set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped unitInterval
namespace ProbabilityTheory.Copula
instance : Subsingleton (Copula 0) where
  allEq C D := ext_cdf (by intro u; simp)
@[simp]
theorem cdf_dim_one (C : Copula 1) (u : Fin 1 → I) : C.cdf u = (u 0 : ℝ) := by
  have hu : u = Function.update (fun _ => 1) 0 (u 0) := by
    funext i
    fin_cases i
    simp
  calc
    C.cdf u = C.cdf (Function.update (fun _ => 1) 0 (u 0)) := congrArg C.cdf hu
    _ = (u 0 : ℝ) := C.cdf_update_one 0 (u 0)
instance : Subsingleton (Copula 1) where
  allEq C D := ext_cdf (by intro u; simp)
end ProbabilityTheory.Copula


