-- Prove2me | Definitions.Def_PermInvCC_ProtoTree
-- name    : PermInvCC_ProtoTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:04.78271+00:00
-- url     : https://prove2.me/theorems/8ecd7d79-4841-4b4f-8071-deda29dff104
-- title:
--   Deterministic two-party protocol trees with outputs
-- statement:
--   A **deterministic protocol tree** has internal nodes owned by Alice or by Bob. At an Alice node Alice sends a bit computed from her input (the position of the node records the transcript so far); at a Bob node Bob does the same; the protocol moves to the child named by the bit. Each leaf carries an output value in a set $\alpha$. The **depth** is the largest number of bits on a root-to-leaf path, and the output on $(x,y)$ is the label of the leaf reached.
--
--   These trees are the deterministic parts of the public-coin protocols of Definition 2.1; outputs may be bits, numbers or sets (Lemmas 3.3 and 3.4).
--
--   **Formalization Note** The output is a function of the transcript, so both parties know it. Local computation is unrestricted.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.1, p.9

import Mathlib

namespace PermInvCC

/-- A **deterministic two-party protocol tree** with outputs in `α` (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.1, p.9: interactive protocols).
At an Alice node Alice sends the bit `f x` computed from her input `x : X`, at a Bob node Bob
sends `g y`; the protocol continues in `p₁` if the bit is `true` and in `p₀` otherwise. Leaves
carry the output.

**Formalization Note.** The preceding transcript is the node's position in the tree, so a node's
bit may depend on the speaker's input and the whole transcript. Local computation is
unrestricted (arbitrary functions). -/
inductive ProtoTree (X Y α : Type) where
  /-- a leaf with output `a` -/
  | leaf (a : α)
  /-- Alice sends `f x` -/
  | alice (f : X → Bool) (p₀ p₁ : ProtoTree X Y α)
  /-- Bob sends `g y` -/
  | bob (g : Y → Bool) (p₀ p₁ : ProtoTree X Y α)

namespace ProtoTree

variable {X Y α : Type}

/-- The **depth** of a protocol tree: the largest number of bits sent along a root-to-leaf
path. -/
def depth : ProtoTree X Y α → ℕ
  | leaf _ => 0
  | alice _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | bob _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- The **output** on `(x, y)`: the label of the leaf reached. It is determined by the
transcript, so both parties know it. -/
def eval : ProtoTree X Y α → X → Y → α
  | leaf a, _, _ => a
  | alice f p₀ p₁, x, y => if f x then p₁.eval x y else p₀.eval x y
  | bob g p₀ p₁, x, y => if g y then p₁.eval x y else p₀.eval x y

end ProtoTree

end PermInvCC


