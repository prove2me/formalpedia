-- Prove2me | Definitions.Def_DetCCHard_Supplement_DaltA
-- name    : DetCCHard_Supplement_DaltA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:37.493713+00:00
-- url     : https://prove2.me/theorems/b8520527-83f2-4c64-b351-c6c64188d697
-- title:
--   Strict alternation with Alice first, and the alternating cost $D^{\mathrm{alt}}_A$
-- statement:
--   In **strict alternation** the two players speak one bit at a time, in turn. A deterministic public-output protocol tree (the published `DetCCHard.Protocol`) is *strictly alternating with Alice first* if Alice speaks at the root and the speakers alternate along every root-to-leaf path: an Alice node occurs only on Alice's turn and both its children are on Bob's turn, and symmetrically; a leaf may end the conversation on either player's turn.
--
--   For a total table $M : X \times Y \to \{0,1\}$, the **alternating cost with Alice first** is
--   $$
--   D^{\mathrm{alt}}_A(M) = \min\{\operatorname{depth}(P) : P \text{ strictly alternating, Alice first, } P(x,y) = M(x,y) \text{ for all } x, y\}.
--   $$
--   Every bit is charged, including fixed bits, and stopping is public: the transcript determines whether communication has ended, because a leaf is a fixed node of the tree.
--
--   This is the cost measure of Theorem 1.2, the fixed-gap hardness result for Yao's original alternating model.
--
--   **Formalization Note** The alternation condition is an inductive predicate `AltFrom aliceTurn P` on the published protocol trees; the cost is the infimum of admissible depths, which is a minimum for finite input sets.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 4.2, p.13

import Mathlib
import Definitions.Def_DetCCHard_Protocol

namespace DetCCHard.Supplement

open DetCCHard

/-- **Strict alternation** (Gaspers–He–Mackenzie, *NP-Hardness and Additive Inapproximability of
Deterministic Communication Complexity*, arXiv:2508.05597, held version sha256 ad552d13…a4a03,
Definition 4.2, p.13: "In strict alternation the players speak one bit at a time, in turn").
`AltFrom aliceTurn P` says that along every root-to-leaf path of the published protocol tree `P`
the speakers alternate, starting with Alice if `aliceTurn = true` and with Bob otherwise: an Alice
node may occur only on Alice's turn and both its children continue on Bob's turn, and symmetrically
for Bob nodes. A leaf ends the communication on either player's turn.

**Formalization Note** Stopping is public, as Definition 4.2 requires: a leaf is a fixed node of
the tree, so the transcript determines whether communication has ended. Every bit, including a
fixed bit (a constant bit function), is charged by `Protocol.depth`. -/
inductive AltFrom {X Y : Type} : Bool → Protocol X Y → Prop
  /-- a leaf may end the communication on either player's turn -/
  | leaf (aliceTurn b : Bool) : AltFrom aliceTurn (Protocol.leaf b)
  /-- on Alice's turn Alice sends one bit; then it is Bob's turn in both children -/
  | alice (f : X → Bool) (p₀ p₁ : Protocol X Y) :
      AltFrom false p₀ → AltFrom false p₁ → AltFrom true (Protocol.alice f p₀ p₁)
  /-- on Bob's turn Bob sends one bit; then it is Alice's turn in both children -/
  | bob (g : Y → Bool) (p₀ p₁ : Protocol X Y) :
      AltFrom true p₀ → AltFrom true p₁ → AltFrom false (Protocol.bob g p₀ p₁)

/-- The **public-output alternating cost with Alice first** `D^alt_A(M)` (Definition 4.2, p.13):
the least depth of a deterministic public-output protocol (published `DetCCHard.Protocol`) in
which the players strictly alternate, Alice speaking first, and which computes every entry of the
total table `M` correctly.

**Formalization Note** For finite input sets the set of admissible depths is nonempty (Alice and
Bob alternately send the bits of their inputs, padding with fixed bits, and the leaves carry the
entries), so the infimum is a minimum and never the junk value of `sInf ∅`. -/
noncomputable def DaltA {X Y : Type} (M : X → Y → Bool) : ℕ :=
  sInf {n : ℕ | ∃ P : Protocol X Y, AltFrom true P ∧ P.depth ≤ n ∧ ∀ x y, P.eval x y = M x y}

end DetCCHard.Supplement


