-- Prove2me | Definitions.Def_CallCountPOPBR_Supplement_RecConsistent
-- name    : CallCountPOPBR_Supplement_RecConsistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:03:25.384015+00:00
-- url     : https://prove2.me/theorems/a0981ebc-79f4-45e8-a3dd-695c586ae746
-- title:
--   Recursively consistent labelled tree families
-- statement:
--   A family $(T_n)_{n\ge0}$ of labelled ordered trees is **recursively consistent** when:
--
--   1. the root of $T_n$ has label $n$;
--   2. at every vertex, every child label is strictly smaller than its parent label;
--   3. every subtree rooted at a vertex labelled $k$ is equal, as a labelled ordered tree, to $T_k$.
--
--   The second and third conditions range over every vertex of every tree in the family.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Section 5.2, p.10

import Definitions.Def_CallCountPOPBR_Supplement_LTree

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Recursively consistent tree families** (§5.2). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §5.2, p.10: "A family of rooted,
integer-labelled trees (T_n) is called recursively consistent if (i) the root of T_n has label n,
(ii) every child label is strictly smaller than its parent label, and (iii) every subtree rooted at
a vertex labelled k is isomorphic as a labelled, ordered tree to T_k."

(ii) and (iii) are required at every vertex of every `T_n` (`LTree.Sub t (T n)` ranges over the
subtrees rooted at the vertices of `T_n`, the root included).

**Formalization Note.** Isomorphism of labelled ordered trees is equality of `LTree` values. -/
def RecConsistent (T : ℕ → LTree) : Prop :=
  (∀ n, (T n).label = n) ∧
  (∀ n t, LTree.Sub t (T n) → ∀ u ∈ t.children, u.label < t.label) ∧
  (∀ n t, LTree.Sub t (T n) → t = T t.label)

end CallCountPOPBR.Supplement


