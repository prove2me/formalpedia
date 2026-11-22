-- Prove2me | Definitions.Def_LeanPool_Copula_Sklar_General
-- name    : LeanPool_Copula_Sklar_General
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:44:37.539902+00:00
-- url     : https://prove2.me/theorems/ea83f5dd-baa6-44f2-8a74-54a3bbae32fe
-- title:
--   General
-- statement:
--   Definitions and structural lemmas for General, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/General.lean

module
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous
public import Definitions.Def_LeanPool_Copula_Sklar_UnitInterval
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval
namespace ProbabilityTheory.Copula
variable {d : ℕ}
end ProbabilityTheory.Copula


