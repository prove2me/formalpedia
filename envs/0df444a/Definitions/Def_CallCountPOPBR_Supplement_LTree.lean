-- Prove2me | Definitions.Def_CallCountPOPBR_Supplement_LTree
-- name    : CallCountPOPBR_Supplement_LTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:02:24.086657+00:00
-- url     : https://prove2.me/theorems/86afe6c0-3667-4f1a-a9c9-50b538a05663
-- title:
--   Finite rooted ordered trees with natural-number labels
-- statement:
--   A labelled ordered tree is a finite rooted tree whose root carries a natural-number label and whose children form an ordered list of labelled ordered trees. The root label, child list, and the relation “$t$ is a subtree rooted at a vertex of $T$” are defined.
--
--   Equality of these inductive trees is equality as labelled ordered trees, including child order.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Section 5.2, p.10

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Finite rooted ordered trees with natural-number labels** (§5.2). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §5.2, p.10:
"A family of rooted, integer-labelled trees (T_n)", compared "as a labelled, ordered tree".

`node l ts` is the tree whose root has label `l` and whose ordered list of child subtrees is `ts`.

**Formalization Note.** Labels are inputs of a decreasing-argument recursion, hence natural numbers.
Two trees are isomorphic as labelled ordered trees iff they are equal as values of this type. -/
inductive LTree where
  | node : ℕ → List LTree → LTree

/-- The label of the root. -/
def LTree.label : LTree → ℕ
  | .node l _ => l

/-- The ordered list of child subtrees of the root. -/
def LTree.children : LTree → List LTree
  | .node _ ts => ts

/-- `Sub t T`: `t` is the subtree of `T` rooted at some vertex of `T` (the root included). -/
inductive LTree.Sub : LTree → LTree → Prop
  | refl (t : LTree) : LTree.Sub t t
  | child {t u : LTree} {l : ℕ} {ts : List LTree} (hu : u ∈ ts) (h : LTree.Sub t u) :
      LTree.Sub t (.node l ts)

end CallCountPOPBR.Supplement


