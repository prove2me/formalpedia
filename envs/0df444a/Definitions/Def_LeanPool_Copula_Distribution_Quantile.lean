-- Prove2me | Definitions.Def_LeanPool_Copula_Distribution_Quantile
-- name    : LeanPool_Copula_Distribution_Quantile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:30.222355+00:00
-- url     : https://prove2.me/theorems/afa0b82d-1553-4ca2-b406-6bcb67337e65
-- title:
--   Quantile
-- statement:
--   Definitions and structural lemmas for Quantile, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Distribution/Quantile.lean

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set Filter
open scoped unitInterval Topology
namespace ProbabilityTheory
@[expose]
noncomputable def unitQuantile (μ : Measure I) (t : I) : I :=
  sSup {x | μ.real (Iic x) < (t : ℝ)}
end ProbabilityTheory


