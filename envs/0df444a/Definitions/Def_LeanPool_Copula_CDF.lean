-- Prove2me | Definitions.Def_LeanPool_Copula_CDF
-- name    : LeanPool_Copula_CDF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:48.852176+00:00
-- url     : https://prove2.me/theorems/bbdd9ef0-4cc5-4e31-b087-a49db47f6628
-- title:
--   CDF
-- statement:
--   Definitions and structural lemmas for CDF, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean

module
public import Definitions.Def_LeanPool_Copula_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval
namespace ProbabilityTheory.Copula
variable {d : ℕ}
@[expose]
noncomputable def cdf (C : Copula d) (u : Fin d → I) : ℝ :=
  C.toMeasure.real (Iic u)
end ProbabilityTheory.Copula


