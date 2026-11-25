-- Prove2me | Definitions.Def_Fekete_DeBruijnErdos
-- name    : Fekete_DeBruijnErdos
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:26:56.309806+00:00
-- url     : https://prove2.me/theorems/e82c6452-cfe6-57fe-8df7-e8c553775c22
-- title:
--   De Bruijn Erdos
-- statement:
--   Definitions and structural lemmas for De Bruijn Erdos, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/DeBruijnErdos.lean

module
public import Definitions.Def_Fekete_Window
public import Mathlib.Analysis.PSeries
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter Finset
open scoped Topology
section Telescoping
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
end Telescoping
namespace NearlySubadditive
variable {f u : ℕ → ℝ} {μ : ℝ} {N : ℕ}
def corr (f : ℕ → ℝ) (c x : ℕ) : ℝ := f (c * x) / (x : ℝ) ^ 2
end NearlySubadditive


