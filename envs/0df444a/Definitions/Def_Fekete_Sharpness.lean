-- Prove2me | Definitions.Def_Fekete_Sharpness
-- name    : Fekete_Sharpness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:33:00.371378+00:00
-- url     : https://prove2.me/theorems/b809f9e1-aaf3-5209-8e3b-713d5219a276
-- title:
--   Sharpness
-- statement:
--   Definitions and structural lemmas for Sharpness, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean

module
public import Definitions.Def_Fekete_DeBruijnErdos
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter Finset
open scoped Topology
namespace NearlySubadditive
def witness (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * ∑ i ∈ range (n + 1), f i / (i : ℝ) ^ 2
variable {f : ℕ → ℝ}
end NearlySubadditive


