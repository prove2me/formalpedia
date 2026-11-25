-- Prove2me | Definitions.Def_Fekete_SupermultiplicativeCounterexample
-- name    : Fekete_SupermultiplicativeCounterexample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:26:26.007803+00:00
-- url     : https://prove2.me/theorems/a355799f-74db-42c7-ba43-84da6985ff53
-- title:
--   Supermultiplicative Counterexample
-- statement:
--   Definitions and structural lemmas for Supermultiplicative Counterexample, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/SupermultiplicativeCounterexample.lean

module
public import Definitions.Def_Fekete_Superadditive
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Filter Topology
namespace Supermultiplicative
noncomputable def evenIndicator (n : ℕ) : ℝ := if Even n then 1 else 0
end Supermultiplicative


