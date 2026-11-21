-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_NodeValidity
-- name    : LinearSetReconciliation327_Main_NodeValidity
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-20T13:07:45.19096+00:00
-- url     : https://prove2.me/theorems/ba23835c-a8c5-4dbb-ad9d-50a5a452cbf4
-- title:
--   Node validity for the HintSketch recursion tree
-- statement:
--   `AllValid` is the node-wise validity predicate of a HintSketch recursion tree.
--
--   At a `store` leaf it is vacuous. At a `cr` leaf (`cr N t`) and at a `direct` node with row scheme `sch` it asserts `Node.Valid N X Y x J`: the stored input $x \subseteq [N]$ has weight at most $X+Y$, the hint $J \subseteq [N]$ has weight at most $X$, and the deviation $x \mathbin{\triangle} J$ has weight at most $Y$.
--
--   At a `recursive` node it asserts the same for the node itself and, recursively, for every child $s$, evaluated at the exact child input $C_s + P_s$ and the exact child hint $J_s$.
--
--   This is the per-node hypothesis under which the tree decoder returns exactly the stored set; it is not an extra assumption, since the root's validity together with the capacity bounds implies it at every node.
-- source:
--   arXiv:2611.11409, §5.4 (HintSketch decoding) and §9.2 (top-level decoder); Theorem 6.5 (main guarantee), conjunct 8. Formal statement extracted verbatim from the Theorem 5.1 development (`Solutions/_51_zzz_full.lean`, §12.6).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Framework

open scoped ENNReal
open Finset

set_option autoImplicit false

noncomputable section

namespace LinearSetReconciliation327.Main


/-! ## 12.5  `AllValid`: `Valid` at every node, and its derivation from the root -/

/-- **`Valid` at every node of the tree**, with the capacities `WF` assigns to each node.

The decode needs this in addition to `AllBounds`.  At a `cr` leaf the only things available are
`t ≤ N` and `min N (X + Y) ≤ t` (`WF`), and `CR.Recovers` additionally wants `x.card ≤ t` — which
needs the *capacity* bound `x.card ≤ X + Y`, a fact about `Valid` alone (`Z`, `U`, `V` say nothing
about it).  `allValid_of_valid` shows the root's `Valid` already gives it. -/
def AllValid (X Y : ℕ) : (T : Node) → Node.Seed T → Finset ℕ → Finset ℕ → Prop
  | .store _, _, _, _ => True
  | .cr N _, _, x, J => Node.Valid N X Y x J
  | .direct sch _, _, x, J => Node.Valid sch.N X Y x J
  | .recursive sch _ Xs Ys child, r, x, J =>
      Node.Valid sch.N X Y x J ∧
        ∀ s, AllValid (Xs s) (Ys s) (child s) (r.2 s)
          (sch.exactChildInput r.1 x J s) (sch.exactHint r.1 x J s)

end LinearSetReconciliation327.Main


