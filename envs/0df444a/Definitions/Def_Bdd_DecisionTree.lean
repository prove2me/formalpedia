-- Prove2me | Definitions.Def_Bdd_DecisionTree
-- name    : Bdd_DecisionTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:37:34.126076+00:00
-- url     : https://prove2.me/theorems/54a8b3f1-6450-4258-b14a-fb6e022a532d
-- title:
--   Decision Tree
-- statement:
--   Definitions and structural lemmas for Decision Tree, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean

import Mathlib.Data.Vector.Basic
set_option autoImplicit true
inductive DecisionTree n where
  | leaf   : Bool  → DecisionTree _
  | branch : Fin n → DecisionTree n → DecisionTree n → DecisionTree n
deriving DecidableEq
namespace DecisionTree
def evaluate : DecisionTree n → Vector Bool n → Bool
  | leaf b, _ => b
  | branch j l h, v => if v[j] then h.evaluate v else l.evaluate v
def size {n} : DecisionTree n → Nat
  | leaf _ => 0
  | branch _ l h => 1 + l.size + h.size
inductive usesVar (i : Fin n) : DecisionTree n → Prop where
  | here : usesVar i (.branch i _ _)
  | low : usesVar i l → usesVar i (.branch _ l _)
  | high : usesVar i h → usesVar i (.branch _ _ h)
def lift : n ≤ n' → DecisionTree n → DecisionTree n'
  | _, .leaf b => .leaf b
  | e, .branch j l h => .branch ⟨j.1, by omega⟩ (lift e l) (lift e h)
def relabel {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n) : DecisionTree n → DecisionTree (f n)
  | .leaf b => .leaf b
  | .branch i l h => .branch ⟨f i, hf i⟩ (relabel hf l) (relabel hf h)
end DecisionTree


