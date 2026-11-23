-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:21.094426+00:00
-- url     : https://prove2.me/theorems/b4cb4d4a-403b-46c3-9564-79f001af1428
-- title:
--   Inhab Rep
-- statement:
--   Definitions and structural lemmas for Inhab Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
abbrev EH (n : ℕ) := EuclideanSpace ℂ (Fin n)
def rsM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EH n)) :=
  ((toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A : EH n →L[ℂ] EH n) : EH n →ₗ[ℂ] EH n).restrict
    (p := ⊤) (q := ⊤) (fun _ _ => Submodule.mem_top)
theorem rsM_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A + rsM B = rsM (A + B) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) + toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A + B) (v : EH n)
  rw [map_add]
  rfl
theorem rsM_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : c • rsM A = rsM (c • A) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show c • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (c • A) (v : EH n)
  rw [map_smul]
  rfl
def rsL (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (⊤ : Submodule ℂ (EH n)) where
  toFun := rsM
  map_add' A B := (rsM_add A B).symm
  map_smul' c A := (rsM_smul c A).symm
end ReciprocityTheory.ChartRestriction.DS


