-- Prove2me | Definitions.Def_LeanPool_Copula_Independence
-- name    : LeanPool_Copula_Independence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:55.123981+00:00
-- url     : https://prove2.me/theorems/a932299c-fc0d-4746-b81a-0f49f6abb0fe
-- title:
--   Independence
-- statement:
--   Definitions and structural lemmas for Independence, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Independence.lean

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Theorems.Thm_ProbabilityTheory_Copula_measurePreserving_eval

set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval BigOperators
namespace ProbabilityTheory.Copula
@[expose]
noncomputable def independence (d : ℕ) : Copula d where
  measure := ⟨Measure.pi (fun _ : Fin d => (volume : Measure I)), inferInstance⟩
  marginal_eq i := (MeasureTheory.measurePreserving_eval (fun _ => volume) i).map_eq
noncomputable instance (d : ℕ) : Inhabited (Copula d) := ⟨independence d⟩
end ProbabilityTheory.Copula


