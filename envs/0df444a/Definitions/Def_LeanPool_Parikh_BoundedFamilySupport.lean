-- Prove2me | Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
-- name    : LeanPool_Parikh_BoundedFamilySupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:48:09.5358+00:00
-- url     : https://prove2.me/theorems/8bd49ce2-6d69-4a2a-824f-b5d6cb513add
-- title:
--   Bounded Family Support
-- statement:
--   Definitions and structural lemmas for Bounded Family Support, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
@[expose] def heightPositions (b H : ℕ) : ℕ := ∑ i ∈ Finset.range (H + 1), b ^ i
namespace ParseTree
variable {T N : Type*}
@[expose] noncomputable def nodeFamily (r : ContextFreeRule T N) (family : Finset (ParseTree T N)) :
    Finset (ParseTree T N) := by
  classical
  exact Finset.univ.image fun f : Fin r.output.length → family =>
    node r (List.ofFn fun i => (f i).val)
end ParseTree
variable {T : Type*} [Fintype T]
@[expose] noncomputable def treeLeaves (g : ContextFreeGrammar T) : Finset (ParseTree T g.NT) := by
  classical
  exact Finset.univ.image ParseTree.terminal ∪ (activeNonterminals g).image ParseTree.hole
@[expose] noncomputable def treeFamily (g : ContextFreeGrammar T) : ℕ → Finset (ParseTree T
  g.NT) := by
  classical
  exact Nat.rec (treeLeaves g) fun _ previous =>
    treeLeaves g ∪ g.rules.biUnion (fun r => ParseTree.nodeFamily r previous)
end Parikh


