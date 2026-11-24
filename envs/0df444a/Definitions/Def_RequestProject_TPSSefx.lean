-- Prove2me | Definitions.Def_RequestProject_TPSSefx
-- name    : RequestProject_TPSSefx
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:26.328882+00:00
-- url     : https://prove2.me/theorems/4b5c25d9-4cc1-4196-89b7-e0b29e6fc423
-- title:
--   TPSSefx
-- statement:
--   Definitions and structural lemmas for TPSSefx, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
def CSafe (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (A : Fin n → Finset G) (q : Fin n → ℝ)
    (i j : Fin n) : Prop :=
  (vbarSum (v i) p (A i) + q i ≥ vbarSum (v i) p (A j) + q j) ∨
  (q j = 0 ∧ (∀ g ∈ A j, p g ≤ v j g) ∧
    ∀ g ∈ A j, vbarSum (v i) p (A i) + q i + eps ≥ vbarSum (v i) p (A j \ {g}) + p g)
end FairSelling


