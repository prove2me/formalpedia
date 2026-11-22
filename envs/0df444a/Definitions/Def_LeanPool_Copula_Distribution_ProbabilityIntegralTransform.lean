-- Prove2me | Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
-- name    : LeanPool_Copula_Distribution_ProbabilityIntegralTransform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:29.303183+00:00
-- url     : https://prove2.me/theorems/3849b4c5-8cc1-41ff-a607-2198bbffac00
-- title:
--   Probability Integral Transform
-- statement:
--   Definitions and structural lemmas for Probability Integral Transform, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/ProbabilityIntegralTransform.lean

module
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.UnitInterval
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set Filter
open scoped unitInterval Topology
namespace ProbabilityTheory
@[expose]
noncomputable def cdfUnit (μ : Measure ℝ) (x : ℝ) : I :=
  ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩
end ProbabilityTheory


