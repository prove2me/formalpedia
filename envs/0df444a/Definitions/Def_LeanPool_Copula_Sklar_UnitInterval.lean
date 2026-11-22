-- Prove2me | Definitions.Def_LeanPool_Copula_Sklar_UnitInterval
-- name    : LeanPool_Copula_Sklar_UnitInterval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:29.658335+00:00
-- url     : https://prove2.me/theorems/279ac168-f481-4dd7-935b-36c3f03ec220
-- title:
--   Unit Interval
-- statement:
--   Definitions and structural lemmas for Unit Interval, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/UnitInterval.lean

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile
public import Definitions.Def_LeanPool_Copula_Sklar_Lift
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval
namespace ProbabilityTheory.Copula
variable {d : ℕ}
@[expose]
noncomputable def unitMarginalCDF (μ : ProbabilityMeasure (Fin d → I)) (i : Fin d) (x : I) : I :=
  by
    letI : IsProbabilityMeasure (μ.toMeasure.map (fun z => z i)) :=
      Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    exact ⟨(μ.toMeasure.map (fun z => z i)).real (Iic x), measureReal_nonneg, measureReal_le_one⟩
end ProbabilityTheory.Copula


