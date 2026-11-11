-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_BinaryTree
-- name    : NoMenuRevenue186_TrustedXOS_BinaryTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:34.50264+00:00
-- url     : https://prove2.me/theorems/23f13218-4dda-416c-811a-21132b870121
-- title:
--   Public binary trees with complete strategies
-- statement:
--   A public communication tree has finitely many binary branches. Each internal node designates either the seller or the buyer as sender, and each leaf carries an outcome. A complete strategy chooses a bit at every transcript where that player sends, including nodes excluded by that strategy's earlier choices. Every pair of complete strategies reaches a leaf.
--
--   The communication cost is the maximum depth of the whole tree:
--
--   $$\mathrm{depth}(\mathrm{leaf})=0,\qquad
--   \mathrm{depth}(\mathrm{node}(T_0,T_1))=1+\max\{\mathrm{depth}(T_0),\mathrm{depth}(T_1)\}.$$
--
--   The transcript representation also assigns unused bits at leaves and at the other player's nodes. These bits are ignored by execution. The interface supports adaptive deviations and charges unsupported executions in exactly the same way as supported ones.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.8–9, PDF p.10–11, Section 2.1

import Mathlib

namespace NoMenuRevenue186.TrustedXOS

/-- Public finite binary tree with a designated sender at every internal node.
    True designates the seller and false the buyer. Section 2.1, printed pp.8–9. -/
inductive BinaryTree (O : Type) where
  | leaf (outcome : O)
  | node (sellerTurn : Bool) (zero one : BinaryTree O)

/-- A complete strategy specifies a bit at every transcript, including off-path nodes. -/
abbrev Strategy := List Bool → Bool

namespace BinaryTree
variable {O : Type}

/-- Execution is total for every pair of complete strategies. -/
def run : BinaryTree O → Strategy → Strategy → List Bool → O
  | .leaf o, _, _, _ => o
  | .node sellerTurn zero one, s, b, h =>
    if (if sellerTurn then s h else b h) then run one s b (h ++ [true])
    else run zero s b (h ++ [false])

/-- Maximum depth of the whole tree, including unsupported and deviating paths. -/
def depth : BinaryTree O → ℕ
  | .leaf _ => 0
  | .node _ zero one => 1 + max zero.depth one.depth

end BinaryTree
end NoMenuRevenue186.TrustedXOS


