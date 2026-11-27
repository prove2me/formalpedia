-- Prove2me | Definitions.Def_TreeStack_Defect
-- name    : TreeStack_Defect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:45:56.166431+00:00
-- url     : https://prove2.me/theorems/81801fca-792b-496f-bed2-1b2fc07e5329
-- title:
--   Defect
-- statement:
--   Definitions and structural lemmas for Defect, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean

import Mathlib
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
namespace TreeStack
noncomputable def scoreDefect
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (v : V) : ℤ :=
  -score T C v
def DefectEdgeState (a b δu δv : ℤ) : Prop :=
  (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
end OrientedBranch
end TreeStack


