-- Prove2me | Definitions.Def_DetCCHard_Protocol
-- name    : DetCCHard_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:00.668123+00:00
-- url     : https://prove2.me/theorems/224fc02c-0ce8-44ec-acd8-e71d9a1e144b
-- title:
--   Deterministic two-party protocol tree, its depth and its output
-- statement:
--   A **deterministic public-output protocol** for two players, Alice holding $x \in X$ and Bob holding $y \in Y$, is a binary tree. Each internal node names a speaker and a bit-valued function of that speaker's input; the protocol moves to the child selected by the transmitted bit. Each leaf carries a fixed output bit. The **depth** of a protocol is the maximum number of bits sent along a root-to-leaf path, and its **output** on $(x, y)$ is the bit at the leaf reached.
--
--   Two auxiliary notions describe the start of a protocol. For a word $w \in \{0,1\}^*$ of bits, the **node at $w$** is the node reached from the root by the transcript $w$ (undefined if $w$ leaves the tree). The **Alice-reach set** of $w$ is the set of Alice inputs $x$ for which every node along $w$ is an Alice node whose bit at $x$ equals the corresponding bit of $w$; it is empty if a Bob node or a leaf occurs along $w$. A node is an **Alice node** if it exists and Alice speaks there.
--
--   These are the objects of Definition 4.1 on which every communication cost in the mission is measured.
--
--   **Formalization Note** A node's bit function takes only the speaker's input: the preceding transcript is the node's position in the tree. A fixed bit is a constant function and is charged like any other bit.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 4.1, p.13

import Mathlib

namespace DetCCHard

/-- A **deterministic public-output two-party protocol** (Gaspers–He–Mackenzie, *NP-Hardness and
Additive Inapproximability of Deterministic Communication Complexity*, arXiv:2508.05597, held
version sha256 ad552d13…a4a03, Definition 4.1, p.13): a binary tree whose internal nodes name a
speaker (Alice, holding `x : X`, or Bob, holding `y : Y`) and a bit-valued function of that
player's input, and whose leaves carry a fixed output bit. At an internal node the protocol moves
to the child `p₁` if the transmitted bit is `true` and to `p₀` otherwise.

**Formalization Note** A node's bit function takes only the speaker's input: the preceding
transcript is the node's position in the tree, so it is already fixed at that node. A fixed bit is
a constant function and is charged like any other bit. -/
inductive Protocol (X Y : Type) where
  /-- a leaf with fixed output `b` -/
  | leaf (b : Bool)
  /-- Alice sends the bit `f x`; continue in `p₁` if it is `true`, in `p₀` otherwise -/
  | alice (f : X → Bool) (p₀ p₁ : Protocol X Y)
  /-- Bob sends the bit `g y`; continue in `p₁` if it is `true`, in `p₀` otherwise -/
  | bob (g : Y → Bool) (p₀ p₁ : Protocol X Y)

namespace Protocol

variable {X Y : Type}

/-- The **depth** (cost) of a protocol: the maximum number of bits sent along a root-to-leaf path
(Definition 4.1, p.13: "Its cost is its maximum depth, charging every bit, including fixed bits"). -/
def depth : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | bob _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- The output of a protocol on the input pair `(x, y)`: follow the bits sent by the players to a
leaf and return its fixed output (Definition 4.1, p.13). -/
def eval : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice f p₀ p₁, x, y => if f x then p₁.eval x y else p₀.eval x y
  | bob g p₀ p₁, x, y => if g y then p₁.eval x y else p₀.eval x y

/-- The node reached from the root by the transcript `w` (a word of bits), or `none` if the
transcript leaves the tree (it continues below a leaf). -/
def nodeAt : Protocol X Y → List Bool → Option (Protocol X Y)
  | p, [] => some p
  | leaf _, _ :: _ => none
  | alice _ p₀ p₁, b :: w => (if b then p₁ else p₀).nodeAt w
  | bob _ p₀ p₁, b :: w => (if b then p₁ else p₀).nodeAt w

/-- The set of Alice's inputs `x` that produce the transcript `w` through Alice nodes only: every
node along `w` (before its end) is an Alice node whose bit at `x` is the corresponding bit of `w`.
It is empty if some node along `w` is a Bob node or a leaf. -/
def aliceReach : Protocol X Y → List Bool → Set X
  | _, [] => Set.univ
  | alice f p₀ p₁, b :: w => {x | f x = b} ∩ (if b then p₁ else p₀).aliceReach w
  | leaf _, _ :: _ => ∅
  | bob _ _ _, _ :: _ => ∅

end Protocol

/-- An optional protocol node is an **Alice node**: it exists and Alice speaks there. -/
def IsAliceNode {X Y : Type} (o : Option (Protocol X Y)) : Prop :=
  ∃ (f : X → Bool) (p₀ p₁ : Protocol X Y), o = some (Protocol.alice f p₀ p₁)

end DetCCHard


