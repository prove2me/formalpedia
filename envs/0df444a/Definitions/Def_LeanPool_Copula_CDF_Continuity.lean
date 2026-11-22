-- Prove2me | Definitions.Def_LeanPool_Copula_CDF_Continuity
-- name    : LeanPool_Copula_CDF_Continuity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:18.395284+00:00
-- url     : https://prove2.me/theorems/be80dd05-a294-405f-aa0c-0e66c2d6582c
-- title:
--   Continuity
-- statement:
--   Definitions and structural lemmas for Continuity, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean

module
public import Definitions.Def_LeanPool_Copula_CDF
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval BigOperators NNReal
namespace ProbabilityTheory.Copula
variable {d : ℕ}
end ProbabilityTheory.Copula


