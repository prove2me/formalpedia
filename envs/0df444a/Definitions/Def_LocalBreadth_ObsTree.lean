-- Prove2me | Definitions.Def_LocalBreadth_ObsTree
-- name    : LocalBreadth_ObsTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:22.685469+00:00
-- url     : https://prove2.me/theorems/0e1c18e3-ebe7-4cea-afae-0b41775457ba
-- title:
--   Admissible obstruction trees
-- statement:
--   Fix a family $\mathcal X$. An **admissible obstruction tree** is a countable rooted tree with language labels such that
--
--   1. a child's label is a language of $\mathcal X$ that is a proper subset of its parent's label;
--   2. if a vertex labelled $L$ has children, then for every finite $F\subseteq L$ there is a child labelled $M$ with $F\subseteq M\subsetneq L$;
--   3. there is no infinite path starting at the root.
--
--   The single-vertex tree is permitted. Such a tree is an adversary's certificate: it keeps a refinement compatible with every finite amount of positive evidence.
--
--   **Formalization Note** A vertex with children is a `ℕ`-indexed family of subtrees (nonempty by the child condition at $F=\emptyset$, repetitions allowed), and clause 3 is the well-foundedness of the inductive type. The root label is the separate condition `T.label = K`, and the root label also lies in $\mathcal X$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Definition 2.3, p.15

import Mathlib

namespace LocalBreadth

/-- A language-labelled well-founded tree, the carrier of an **admissible obstruction tree**.
Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), Definition 2.3, p.15.

**Formalization Note.** A vertex with children has a nonempty countable family of them (clause 3 at
`F = ∅`), written as a `ℕ`-indexed family with repetitions allowed; repeated subtrees do not change
the set of root-to-leaf paths. Clause 4, no infinite path, is the inductive type's well-foundedness.
Conversely a well-founded `ℕ`-branching tree is countable. -/
inductive ObsTree where
  /-- A vertex with no children, labelled `L`. -/
  | leaf (L : Set ℤ) : ObsTree
  /-- A vertex labelled `L` with children `c`. -/
  | node (L : Set ℤ) (c : ℕ → ObsTree) : ObsTree

namespace ObsTree

/-- The label of the root. -/
def label : ObsTree → Set ℤ
  | leaf L => L
  | node L _ => L

/-- Definition 2.3: every label is a language of `X`, a child's label is a proper subset of its
parent's, and a vertex labelled `L` with children has, for every finite `F ⊆ L`, a child whose label
contains `F`. "The root is labelled `K`" is the separate condition `T.label = K`. -/
def Admissible (X : Set (Set ℤ)) : ObsTree → Prop
  | leaf L => L ∈ X
  | node L c => L ∈ X ∧ (∀ i, (c i).label ⊂ L ∧ Admissible X (c i)) ∧
      ∀ F : Finset ℤ, (F : Set ℤ) ⊆ L → ∃ i, (F : Set ℤ) ⊆ (c i).label

/-- The root-to-leaf paths, read as lists of labels, root first. -/
def paths : ObsTree → Set (List (Set ℤ))
  | leaf L => {[L]}
  | node L c => {p | ∃ i, ∃ q ∈ paths (c i), p = L :: q}

end ObsTree

end LocalBreadth


