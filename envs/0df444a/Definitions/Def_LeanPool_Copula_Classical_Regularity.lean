-- Prove2me | Definitions.Def_LeanPool_Copula_Classical_Regularity
-- name    : LeanPool_Copula_Classical_Regularity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:51:11.273543+00:00
-- url     : https://prove2.me/theorems/0806cacc-1c89-464b-ae8a-2b0b7f96860c
-- title:
--   Regularity
-- statement:
--   Definitions and structural lemmas for Regularity, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Set
open scoped unitInterval BigOperators NNReal
namespace ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
end ProbabilityTheory.Copula


