-- Prove2me | Definitions.Def_CLRS_Chapter4_RecursionTree
-- name    : CLRS_Chapter4_RecursionTree
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:50.918859+00:00
-- url     : https://prove2.me/theorems/94c178a0-2ede-404d-86aa-bd5dafcf4eb9
-- title:
--   Finite ordered recursion trees and exact cost accounting
-- statement:
--   Each node of a finite ordered recursion tree has a natural root size, natural local work, and a finite list of subtrees. Definitions supply total work, height, level work, finite sums, and consistency with prescribed child lists, base work, toll, and cutoff. Below cutoff, a consistent node is a base leaf; otherwise it uses the toll and prescribed ordered children. Weighted toll sums record balanced depth unrolling. Shapes may be unbalanced and contain repeated child sizes.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module RecursionTree, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/RecursionTree.lean

import Definitions.Def_CLRS_Chapter4_Substitution
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-!
Generic finite recursion-tree accounting. Branching factors and child heights
may differ at every node. Work is a mathematical natural-number charge attached
to a call; these theorems do not assume a balanced or fixed-arity call tree.
-/

namespace Chapter4RecursionTree

/-- A call records its input size, its own work, and its ordered recursive calls. -/
inductive Tree where
  | node (size work : Nat) (children : List Tree)

def Tree.rootSize : Tree → Nat
  | .node size _ _ => size



def Tree.totalCost : Tree → Nat
  | .node _ work children => work + (children.map Tree.totalCost).sum

/-- Height counts the root level, so a leaf has height one. -/
def Tree.height : Tree → Nat
  | .node _ _ children => 1 + (children.map Tree.height).foldr max 0



def Tree.levelCost : Tree → Nat → Nat
  | .node _ work _, 0 => work
  | .node _ _ children, depth+1 => (children.map (fun child => child.levelCost depth)).sum

/-- The sum of f(0), ..., f(count-1), with an empty sum at count zero. -/
def sumBelow : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | count+1, f => sumBelow count f + f count






































/-- A finite tree follows a size recurrence. Base work is explicit; internal
nodes use exactly the prescribed child list, including repeated children. -/
inductive Consistent (children : Nat → List Nat) (toll base : Nat → Nat) (cutoff : Nat) : Tree → Prop where
  | leaf (size : Nat) (small : size < cutoff) :
      Consistent children toll base cutoff (.node size (base size) [])
  | branch (size : Nat) (forest : List Tree) (large : cutoff ≤ size)
      (sizes : forest.map Tree.rootSize = children size)
      (subtrees : ∀ tree ∈ forest, Consistent children toll base cutoff tree) :
      Consistent children toll base cutoff (.node size (toll size) forest)













/-- Internal-level contribution to T(k+1)=a*T(k)+g(k), written as an explicit
finite weighted sum. The exponent counts ancestors duplicating that work. -/
def weightedTolls (arity depth : Nat) (toll : Nat → Nat) : Nat :=
  sumBelow depth (fun level => arity^(depth-1-level)*toll level)

















end Chapter4RecursionTree

end CLRS


