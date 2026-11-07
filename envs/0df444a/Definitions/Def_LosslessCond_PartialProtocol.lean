-- Prove2me | Definitions.Def_LosslessCond_PartialProtocol
-- name    : LosslessCond_PartialProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:27.712945+00:00
-- url     : https://prove2.me/theorems/2288c39f-4a60-4c65-ad62-f9ae2e67e42f
-- title:
--   Partial protocol on a complete depth-$s$ tree, Bob assignments and runs
-- statement:
--   A **partial protocol** of depth $s$ is a complete binary tree of depth $s$ in which every speaker and every leaf output is fixed, Alice's message functions are given, and Bob's message functions are left unspecified. Inductively:
--
--   1. a leaf with output $b\in\{0,1\}$ is a partial protocol of depth $0$;
--   2. if $P_0,P_1$ have depth $s$ and $f:X\to\{0,1\}$, the Alice node "send $f(x)$, continue in $P_{f(x)}$" has depth $s+1$;
--   3. if $P_0,P_1$ have depth $s$, a Bob node with children $P_0,P_1$ (and no message function) has depth $s+1$.
--
--   A **Bob assignment** $\beta$ chooses one bit at every Bob node of the tree. Given $\beta$ and Alice's row $x$, the **run** of the tree follows $f(x)$ at Alice nodes and the assigned bit at Bob nodes, and returns the output of the leaf reached.
--
--   These are the objects of Definition 3.1 whose domains the paper counts.
--
--   **Formalization Note** Alice's message functions are given on all of $X$; the paper specifies them on the retained row set $U$ only, and only those values matter. Bit $1$ selects the child $P_1$.
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Definition 3.1, p.8 (PDF p.9)

import Mathlib

namespace LosslessCond

/-- A **partial protocol** on a complete binary tree of depth `s` (Mackenzie, *Lossless Hardness
Condensation in Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256
ce75e6d4…, Definition 3.1, p.8): every speaker and every leaf output is fixed, Alice's message
functions are given, and Bob's message functions are left unspecified.

* `leaf b` is a leaf (depth `0`) with output `b`;
* `alice f p₀ p₁` is an Alice node: she sends the bit `f x`, and the protocol continues in `p₁` if
  it is `true` and in `p₀` otherwise;
* `bob p₀ p₁` is a Bob node whose bit is not specified.

Both children of a node of depth `s + 1` have depth `s`, so the tree is complete of depth `s`.

**Formalization Note** Alice's message function is given on all of `X`; the paper specifies it
only on the retained row set `U`, and only its values on `U` ever matter. Bit `true` selects the
child `p₁`, as in `DetCCHard.Protocol`. -/
inductive PartialProtocol (X : Type) : ℕ → Type
  /-- a leaf with fixed output `b` -/
  | leaf (b : Bool) : PartialProtocol X 0
  /-- an Alice node sending `f x` -/
  | alice {s : ℕ} (f : X → Bool) (p₀ p₁ : PartialProtocol X s) : PartialProtocol X (s + 1)
  /-- a Bob node with unspecified message -/
  | bob {s : ℕ} (p₀ p₁ : PartialProtocol X s) : PartialProtocol X (s + 1)

namespace PartialProtocol

variable {X : Type}

/-- An **assignment of bits to all Bob nodes** of a partial protocol (Definition 3.1, p.8): one bit
at each Bob node, and nothing at leaves or Alice nodes. -/
def BobBits : {s : ℕ} → PartialProtocol X s → Type
  | _, leaf _ => Unit
  | _, alice _ p₀ p₁ => BobBits p₀ × BobBits p₁
  | _, bob p₀ p₁ => Bool × BobBits p₀ × BobBits p₁

/-- The output of the tree on Alice's row `x` when the Bob nodes send the bits `β`: Alice nodes
follow `f x`, Bob nodes follow their assigned bit, and the leaf reached gives the output. -/
def run : {s : ℕ} → (P : PartialProtocol X s) → BobBits P → X → Bool
  | _, leaf b, _, _ => b
  | _, alice f p₀ p₁, β, x => if f x then run p₁ β.2 x else run p₀ β.1 x
  | _, bob p₀ p₁, β, x => if β.1 then run p₁ β.2.2 x else run p₀ β.2.1 x

end PartialProtocol

end LosslessCond


