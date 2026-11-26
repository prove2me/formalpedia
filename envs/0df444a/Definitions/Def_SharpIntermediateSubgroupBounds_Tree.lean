-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Tree
-- name    : SharpIntermediateSubgroupBounds_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:40:40.854978+00:00
-- url     : https://prove2.me/theorems/e66cef44-7e45-451c-b092-2a618808ea93
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Tree.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace BranchingTree
universe u
variable {State : Type*}
variable (Choice : State → Type*) [∀ s, Fintype (Choice s)]
variable (next : ∀ s, Choice s → State)
def Path : ℕ → State → Type _
  | 0, _ => PUnit
  | r + 1, s => Σ x : Choice s, Path r (next s x)
noncomputable instance pathFintype (r : ℕ) (s : State) :
    Fintype (Path Choice next r s) := by
  induction r generalizing s with
  | zero =>
      simp only [Path]
      infer_instance
  | succ r ih =>
      simp only [Path]
      letI (x : Choice s) : Fintype (Path Choice next r (next s x)) := ih (next s x)
      infer_instance
def branchProduct : ∀ {r s}, Path Choice next r s → ℕ
  | 0, _, _ => 1
  | _ + 1, s, ⟨x, z⟩ => Fintype.card (Choice s) * branchProduct z
end BranchingTree
end SharpIntermediateSubgroupBounds


