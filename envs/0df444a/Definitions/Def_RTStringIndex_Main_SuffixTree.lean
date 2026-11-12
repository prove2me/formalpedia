-- Prove2me | Definitions.Def_RTStringIndex_Main_SuffixTree
-- name    : RTStringIndex_Main_SuffixTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:08.522877+00:00
-- url     : https://prove2.me/theorems/546d8650-1360-4ec8-b49d-fca60c335fa5
-- title:
--   The suffix tree of a text through its labels: nodes, weights, Weiner marks and $R(v)$
-- statement:
--   The suffix tree of a text $x$ is described through the labels of its locations. Its leaves are the $|x|+1$ suffixes of $x\$$. A **location** is a prefix of a leaf; it is an **explicit node** if it is the root, a leaf, or **branching** (followed by two different symbols). The ancestor relation is the prefix order, the string depth is the length, $\mathrm{slink}$ removes the first symbol, and the $\mathrm{lca}$ of two nodes is the longest common prefix of their labels.
--
--   The **weight** of a location $u$ is the number of leaves below it. A leaf $y$ is **marked** with the letter $a$ when $a\cdot y$ is also a leaf (the Weiner link of $y$ labelled $a$); thus the leaf of $T[i..]$ with $i\ge 2$ is marked $T[i-1]$.
--
--   For a small subtree rooted at $a\cdot v$, with $\mathrm{slink}(a\cdot v)=v$,
--   $$R(v)=\{\mathrm{slink}(x) : x \text{ a leaf below } a\cdot v\}$$
--   is the set of leaves below $v$ marked with $a$. $L$ is the set of labels of nodes of weight at least $2\tau$.
--
--   These are the objects of §2, §3, §6 and §7 on which the path-decomposed suffix tree is built.
--
--   **Formalization Note** The tree is the compacted trie of the set of suffixes, so it is determined by the text; nodes are identified with their labels.
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), §2, pp. 2–3 (locations, label, strdepth, slink, lca); §3, p. 5 (weight); §6, p. 12 (R(v')), p. 15 (marks); §7, p. 18 (L); PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_Strings

set_option autoImplicit false

namespace RTStringIndex.Main

/-! # The suffix tree of a text, described through its labels

Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), §2, pp.2–3: "A location (or locus)
in the suffix tree is either an explicit node or an implicit node located on an edge. Thus, each
location corresponds to a distinct substring … label(ν) … strdepth(ν) … slink(u) … lca(u, v)";
§3, p.5: "Let the weight of a node u denote the number of leaves in the subtree rooted at u";
§6, p.15: "Every leaf is marked by the symbol of its Weiner link … a leaf holding the suffix
T[i..n], with i > 1, is marked by T[i − 1]"; §6, p.12: `R(v′)`.

**Formalization Note.** A location is identified with its label, a string over `Chr`. The tree of
the text `x` is the compacted trie of the set `sufSet x` of the `|x| + 1` suffixes of `x$`
(including `$` itself); every suffix is a leaf. For a finite set `S` of strings: the locations are
the prefixes of members of `S`; the explicit nodes are the root `[]`, the members of `S` (leaves),
and the branching locations (followed by two different symbols). Ancestor is the prefix order,
`strdepth` is the length, `slink` removes the first symbol, and `lca` of two nodes is the longest
common prefix of their labels (`lcpStr`). The weight of a location is the number of leaves below
it. -/

open Classical

/-- The leaves of the suffix tree of `x`: the `|x| + 1` suffixes of `x$`. -/
noncomputable def sufSet (x : List ℕ) : Finset (List Chr) :=
  (Finset.range (x.length + 1)).image (fun j => term (x.drop j))

/-- `ν` is a location of the trie of `S`: a prefix of some string of `S`. -/
def IsLoc (S : Finset (List Chr)) (ν : List Chr) : Prop := ∃ y ∈ S, ν <+: y

/-- The weight of a location: the number of leaves below it. -/
noncomputable def weight (S : Finset (List Chr)) (ν : List Chr) : ℕ :=
  (S.filter (fun y => ν <+: y)).card

/-- A branching location: followed by two different symbols. -/
def IsBranching (S : Finset (List Chr)) (ν : List Chr) : Prop :=
  ∃ a b : Chr, a ≠ b ∧ IsLoc S (ν ++ [a]) ∧ IsLoc S (ν ++ [b])

/-- An explicit node: the root, a leaf, or a branching location. -/
def IsNode (S : Finset (List Chr)) (ν : List Chr) : Prop :=
  IsLoc S ν ∧ (ν = [] ∨ ν ∈ S ∨ IsBranching S ν)

/-- An internal node: an explicit node that is not a leaf. -/
def IsInternal (S : Finset (List Chr)) (ν : List Chr) : Prop := IsNode S ν ∧ ν ∉ S

/-- `p` is the parent of the node `x`: the lowest node that is a proper ancestor of `x`. -/
def IsParent (S : Finset (List Chr)) (p x : List Chr) : Prop :=
  IsNode S p ∧ IsNode S x ∧ p <+: x ∧ p ≠ x ∧
    ∀ q, IsNode S q → p <+: q → q <+: x → q = p ∨ q = x

/-- The leaf `y` is marked with the letter `a`: `a·y` is also a leaf (the Weiner link of `y`
labelled `a`); the leaf of `T[i..]$` with `i ≥ 1` is marked `T[i−1]`. -/
def IsMarked (S : Finset (List Chr)) (y : List Chr) (a : ℕ) : Prop := ((a : Chr) :: y) ∈ S

/-- The number of leaves below the location `u` that are marked with `a`. -/
noncomputable def markCount (S : Finset (List Chr)) (u : List Chr) (a : ℕ) : ℕ :=
  (S.filter (fun y => u <+: y ∧ IsMarked S y a)).card

/-- `R(v)` for the letter `a` (§6, p.12): for a small subtree `T(a·v)` with `slink(a·v) = v`, the
set `{slink(x) : x a leaf below a·v}`, i.e. the leaves below `v` that are marked with `a`. -/
noncomputable def Rset (S : Finset (List Chr)) (a : ℕ) (v : List Chr) : Finset (List Chr) :=
  S.filter (fun y => v <+: y ∧ IsMarked S y a)

/-- The labels of the nodes of weight at least `2τ` (the set `L` of §7, p.18). -/
noncomputable def heavyLabels (S : Finset (List Chr)) (τ : ℝ) : Finset (List Chr) :=
  (S.biUnion (fun y => y.inits.toFinset)).filter
    (fun x => IsNode S x ∧ 2 * τ ≤ (weight S x : ℝ))

end RTStringIndex.Main


