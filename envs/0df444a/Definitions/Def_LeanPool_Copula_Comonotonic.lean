-- Prove2me | Definitions.Def_LeanPool_Copula_Comonotonic
-- name    : LeanPool_Copula_Comonotonic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:19.886487+00:00
-- url     : https://prove2.me/theorems/fdd3e3b2-9582-42e7-9099-7bbeacb6147c
-- title:
--   Comonotonic
-- statement:
--   Definitions and structural lemmas for Comonotonic, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Comonotonic.lean

module
public import Definitions.Def_LeanPool_Copula_CDF
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory
open scoped unitInterval
namespace ProbabilityTheory.Copula
@[expose]
noncomputable def comonotonic (d : ℕ) : Copula d :=
  ofMap ⟨volume, inferInstance⟩ (fun u _ => u)
    (measurable_pi_iff.mpr fun _ => measurable_id) (fun _ => Measure.map_id)
end ProbabilityTheory.Copula


