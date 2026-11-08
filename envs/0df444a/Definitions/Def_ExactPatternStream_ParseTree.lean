-- Prove2me | Definitions.Def_ExactPatternStream_ParseTree
-- name    : ExactPatternStream_ParseTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:14.232777+00:00
-- url     : https://prove2.me/theorems/aaa9d3e7-ce33-4cf5-ab7d-3cc919526cba
-- title:
--   §4.3 — labels, parse trees, leaves and wt
-- statement:
--   Nodes have labels: a character of $\Sigma$, the guard $\$$, a marker $\#_i$, or a positive-level label $(y,z,\alpha)$ of §7.3. Leaves are characters of $\Sigma$, $\$$ or the single marker $\#$. $\mathrm{leaves}(\#_i)=\#^{w_i}$, and for every other node, $\mathrm{leaves}$ lists the subtree leaves from left to right. $\mathrm{wt}(S)=|\{x:S[x]\in\Sigma\}|$.
--
--   The parse trees retain every label and annotation, as the forests $\mathrm{subtrees}(U)$ of §5 do: equal lists of trees are equal forests.
--
--   **Formalization Note** One `Label` type serves all levels. A `ParseTree` node carries its annotation in its own level ($A_i$), and each child also its annotation in the padded level ($\hat A_i$), so "every annotation" is retained in both readings of p.13. An inserted padding node is a one-node tree recording $w_i$.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §4.2–§4.3, pp.8–11 (PDF 9–12); §5, p.13 (PDF 14); p.21 (PDF 22) for wt

import Mathlib

namespace ExactPatternStream

/-! # Labels and parse trees

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §4.2–§4.3, pp.8–11 (PDF 9–12), and
§5, p.13 (PDF 14) for `subtrees`.

**Formalization Note.** One `Label` type serves all levels: a raw symbol, the guard `$`, the marker
`#ᵢ`, and a positive-level node `(y, z, α)` of §7.3 (`y` a bit string, `z` a counter `(M, s)`, `α` a bit).
Leaves are raw symbols, `$`, or the single marker `#`, as on p.11. A `ParseTree` retains every label and
annotation, so that equal lists of trees are the paper's equal forests `subtrees(U)`: `active` is the
annotation of the node at its own level (`A_i`), and each child also carries its annotation in the padded
level (`Â_i`). An inserted padding node is a one-node tree, and `leaves(#ᵢ) = #^{wᵢ}`, so it records `wᵢ`. -/

/-- The symbols at leaves: a character of `Σ`, the guard `$`, or the marker `#`. -/
inductive Leaf where
  | sym (a : ℕ)
  | guard
  | hash
  deriving DecidableEq, Repr, Inhabited

/-- Node labels at all levels. -/
inductive Label where
  | raw (a : ℕ)
  | guard
  | marker (i : ℕ)
  | node (y : List Bool) (z : ℕ × ℕ) (α : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- A node of a parse tree with its full subtree. -/
inductive ParseTree where
  /-- A level-0 node with its label `l` (as a leaf) and its annotation. -/
  | base (l : Leaf) (active : Bool)
  /-- An inserted marker `#ᵢ` at level `i`, of width `w = wᵢ`. -/
  | padding (i w : ℕ)
  /-- A positive-level node: label, annotation, and children with their padded-level annotations. -/
  | node (label : Label) (active : Bool) (children : List (Bool × ParseTree))
  deriving Inhabited

namespace ParseTree

/-- The label of the root. -/
def label : ParseTree → Label
  | base (Leaf.sym a) _ => Label.raw a
  | base Leaf.guard _ => Label.guard
  | base Leaf.hash _ => Label.guard
  | padding i _ => Label.marker i
  | node l _ _ => l

mutual
  /-- `leaves(v)`: the subtree leaves from left to right; `leaves(#ᵢ) = #^{wᵢ}`. -/
  def leaves : ParseTree → List Leaf
    | base l _ => [l]
    | padding _ w => List.replicate w Leaf.hash
    | node _ _ cs => leavesChildren cs

  /-- Leaves of a list of annotated children. -/
  def leavesChildren : List (Bool × ParseTree) → List Leaf
    | [] => []
    | (_, t) :: ts => leaves t ++ leavesChildren ts
end

end ParseTree

/-- `leaves` extended to node strings by concatenation. -/
def leavesOf (ts : List ParseTree) : List Leaf := ts.flatMap ParseTree.leaves

/-- The labels of a node string. -/
def labels (ts : List ParseTree) : List Label := ts.map ParseTree.label

/-- `wt(S) = |{x : S[x] ∈ Σ}|`, p.21. -/
def wt (S : List Leaf) : ℕ :=
  (S.filter fun l => match l with | Leaf.sym _ => true | _ => false).length

end ExactPatternStream


