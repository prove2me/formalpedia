-- Prove2me | Definitions.Def_LosslessCond_Supplement_MultiProtocol
-- name    : LosslessCond_Supplement_MultiProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:24:28.491798+00:00
-- url     : https://prove2.me/theorems/f7b8b704-56b3-41e5-8235-f68357387e84
-- title:
--   Deterministic $p$-party number-in-hand protocol with outputs in $Z$
-- statement:
--   Fix $p$ players; player $i$ holds an input $x_i\in X_i$. A **deterministic number-in-hand protocol** with outputs in a set $Z$ is a binary tree. Communication is written on a public blackboard: at each internal node the tree names the next speaker $i$ and a function $f:X_i\to\{0,1\}$, and player $i$ writes the bit $f(x_i)$; the protocol moves to the right child on $1$ and to the left child on $0$. Each leaf carries a fixed label $z\in Z$, which is the output.
--
--   Since the node is determined by the transcript so far, each transmitted bit depends only on the speaker's input and the transcript, and the speaking order is chosen by the transcript (players need not alternate). The **depth** of a protocol is the largest number of bits written along a root-to-leaf path, every bit charged, including constant bits; its **value** on an input tuple $x=(x_1,\dots,x_p)$ is the label of the leaf reached.
--
--   This is the communication model of Appendix B, in which the paper's multiparty condensation and local-to-global theorems are stated.
--
--   **Formalization Note** Players are indexed by `Fin p` and the inputs form a dependent family `X : Fin p → Type`; the definition mirrors the two-party `DetCCHard.Protocol`, with a speaker index in place of the Alice/Bob distinction and leaves in `Z` in place of `Bool`.
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Appendix B, pp.25–26 (PDF pp.26–27)

import Mathlib

namespace LosslessCond

namespace Supplement

/-- A **deterministic `p`-party number-in-hand protocol with outputs in `Z`** (Mackenzie, *Lossless
Hardness Condensation in Deterministic Communication Complexity*, arXiv:2609.28691, held version
sha256 ce75e6d4…, Appendix B, pp.25–26, PDF pp.26–27): player `i` holds `x i : X i`;
communication is written on a public blackboard, the next speaker is determined by the transcript,
a transmitted bit depends only on that speaker's input and the transcript, and leaves have fixed
labels in `Z`.

* `leaf z` is a leaf with fixed output `z`;
* `send i f P₀ P₁` is a node at which player `i` writes the bit `f (x i)`; the protocol continues in
  `P₁` if the bit is `true` and in `P₀` otherwise.

**Formalization Note** The transcript so far is the node's position in the tree, so a message
depending on the speaker's input and the transcript is a function `X i → Bool` at each node, and the
speaker `i` at each node is chosen by the tree (players need not alternate or speak in a fixed
order). This mirrors the two-party `DetCCHard.Protocol`. -/
inductive MultiProtocol {p : ℕ} (X : Fin p → Type) (Z : Type) : Type
  /-- a leaf with fixed output `z` -/
  | leaf (z : Z)
  /-- player `i` writes the bit `f (x i)`; continue in `P₁` if it is `true`, in `P₀` otherwise -/
  | send (i : Fin p) (f : X i → Bool) (P₀ P₁ : MultiProtocol X Z)

namespace MultiProtocol

variable {p : ℕ} {X : Fin p → Type} {Z : Type}

/-- The **depth** (worst-case number of communicated bits) of a protocol: the maximum number of
bits written along a root-to-leaf path. Every bit is charged, including constant bits. -/
def depth : MultiProtocol X Z → ℕ
  | leaf _ => 0
  | send _ _ P₀ P₁ => max P₀.depth P₁.depth + 1

/-- The output of a protocol on the input tuple `x`: follow the written bits to a leaf and return its
fixed label. -/
def eval : MultiProtocol X Z → (∀ i, X i) → Z
  | leaf z, _ => z
  | send i f P₀ P₁, x => if f (x i) then P₁.eval x else P₀.eval x

end MultiProtocol

end Supplement

end LosslessCond


