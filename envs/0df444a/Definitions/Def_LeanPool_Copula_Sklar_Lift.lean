-- Prove2me | Definitions.Def_LeanPool_Copula_Sklar_Lift
-- name    : LeanPool_Copula_Sklar_Lift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:54.451489+00:00
-- url     : https://prove2.me/theorems/c6dc89df-e401-4ad3-8b01-24e6640863e1
-- title:
--   Lift
-- statement:
--   Definitions and structural lemmas for Lift, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Sklar/Lift.lean

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_Distribution_RandomizedInverse
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set Filter Function
open scoped unitInterval
namespace ProbabilityTheory.Copula
end ProbabilityTheory.Copula


