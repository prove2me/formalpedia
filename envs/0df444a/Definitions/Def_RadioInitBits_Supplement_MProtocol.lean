-- Prove2me | Definitions.Def_RadioInitBits_Supplement_MProtocol
-- name    : RadioInitBits_Supplement_MProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:05:01.54182+00:00
-- url     : https://prove2.me/theorems/c96abeb3-fcba-45b2-9da9-6f42495fa681
-- title:
--   Anonymous radio protocols with multi-bit messages, their energy, message length and $(1-f)$-initialization (Definition 8)
-- statement:
--   An **anonymous randomized protocol with multi-bit messages** is one piece of code that every node runs:
--
--   1. a state space and an initial state $\mathrm{init}(s)$ computed from the node's private seed $s$ (the published seeds `RadioInitBits.Seed`, i.i.d. uniform streams);
--   2. for each round $r=0,1,2,\dots$ and state $x$, an action $\mathrm{act}(r,x)$: sleep, listen, or transmit a message;
--   3. an update rule $x\mapsto\mathrm{update}(r,x,o)$ after observing $o$ on the multi-bit no-CD channel;
--   4. a fixed number $R$ of rounds and an output map giving each final state an ID $k\in\mathbb N$ or the mark "uninitialized".
--
--   The **execution** on seeds $\omega=(\omega_1,\dots,\omega_n)$ runs all nodes in lockstep. On top of it the definition provides:
--
--   1. the **energy** of node $i$: the number of rounds $r<R$ in which $i$ transmits or listens;
--   2. the predicate "**messages have at most $L$ bits**": in every execution every transmitted message has length at most $L$;
--   3. **(1 − f)-initialization** (Definition 8): with $K$ the number of nodes that output an ID, every ID lies in $\{1,\dots,K\}$, no two nodes output the same ID (so the IDs are exactly $1,\dots,K$), and
--   $$K\ \ge\ (1-f)\,n,$$
--   that is, at most $fn$ nodes are marked uninitialized.
--
--   These are the model, the cost measures and the success event of Theorem 3.
--
--   **Formalization Note** Definition 8 reads "number all but $fn$ nodes … with distinct IDs from 1 to $(1-f)n$". Since $fn$ need not be an integer this is read as "all but at most $fn$, carrying exactly the IDs $1,\dots,K$ with $K\ge(1-f)n$", which is what the proof of Theorem 3 delivers. For $f<1/n$ it is full initialization, as in the published `RadioInitBits.Protocol.Initialized`. The number of rounds is fixed in advance.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version §2.1, pp.4–5 (PDF pp.25–26) (energy, p.5) and §2.2, Definition 8, p.5 (PDF p.26)

import Mathlib
import Definitions.Def_RadioInitBits_seedLaw
import Definitions.Def_RadioInitBits_Supplement_mobserve

set_option autoImplicit false

namespace RadioInitBits

namespace Supplement

/-- An **anonymous randomized protocol** for a single-hop radio network with **multi-bit
messages** and no collision detection. Every node runs the same code:

* `init s` is the node's initial state, computed from its private seed `s` (the published
  `RadioInitBits.Seed`);
* in round `r` (rounds are numbered `0, 1, 2, …`) a node in state `x` takes the action `act r x`
  (sleep, listen, or send a message);
* after round `r` it moves to state `update r x o`, where `o` is what it observed in round `r`;
* the protocol runs for `rounds` rounds, after which a node in state `x` outputs `output x`
  (`some k`: the ID `k`; `none`: marked "uninitialized").

D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version §2.1, pp.4–5 (PDF pp.25–26).

**Formalization Note** The same shape as the published single-bit `RadioInitBits.Protocol`, with
the multi-bit actions `MAction` and observations `MObs`. No node identifier appears in a protocol.
"All nodes know n" (and, in Theorem 3, the parameter `f`) is modelled by protocol families indexed
by them. The number of rounds is fixed in advance. -/
structure MProtocol where
  /-- The local state space of a node. -/
  State : Type
  /-- The initial state, computed from the node's private seed. -/
  init : Seed → State
  /-- The action taken in round `r` in state `x`. -/
  act : ℕ → State → MAction
  /-- The state after round `r`, given the state before it and the observation in it. -/
  update : ℕ → State → MObs → State
  /-- The output (an ID, or `none` = uninitialized) of a node in final state `x`. -/
  output : State → Option ℕ
  /-- The number of rounds the protocol runs. -/
  rounds : ℕ

namespace MProtocol

/-- The **execution** of `P` on `n` nodes with seeds `ω`: `P.config ω r i` is the state of node
`i` before round `r`. In round `r` all nodes act simultaneously, each node observes the no-CD
multi-bit channel `mobserve` applied to the actions of all nodes, and updates its state. -/
noncomputable def config (P : MProtocol) {n : ℕ} (ω : Fin n → Seed) : ℕ → Fin n → P.State
  | 0 => fun i => P.init (ω i)
  | r + 1 => fun i =>
      P.update r (config P ω r i) (mobserve (fun j => P.act r (config P ω r j)) i)

/-- The **energy spent** by node `i` in the execution of `P` with seeds `ω`: the number of rounds
`r < P.rounds` in which `i` transmits or listens.
Banasik, Dani, Hayes, full version §2.1, p.5 (PDF p.26): "The energy spent by a node is the total
number of rounds in which it transmits or listens. The energy complexity of an algorithm is the
maximum energy spent, taken over all nodes." -/
noncomputable def energy (P : MProtocol) {n : ℕ} (ω : Fin n → Seed) (i : Fin n) : ℕ :=
  ((Finset.range P.rounds).filter fun r => P.act r (P.config ω r i) ≠ MAction.sleep).card

/-- The output of node `i` at the end of the execution of `P` with seeds `ω`. -/
noncomputable def out (P : MProtocol) {n : ℕ} (ω : Fin n → Seed) (i : Fin n) : Option ℕ :=
  P.output (P.config ω P.rounds i)

/-- `P` run on `n` nodes uses messages of at most `L` bits: in every execution, every message
transmitted in a round `r < P.rounds` has length at most `L`.
Banasik, Dani, Hayes, full version §2.1, p.5 (PDF p.26): "In Section 4, we assume O(log n)-bit
message sizes". -/
def MsgBounded (P : MProtocol) (n : ℕ) (L : ℝ) : Prop :=
  ∀ (ω : Fin n → Seed) (r : ℕ) (i : Fin n) (m : List Bool),
    r < P.rounds → P.act r (P.config ω r i) = MAction.send m → (m.length : ℝ) ≤ L

/-- The execution of `P` on `n` nodes with seeds `ω` **solves (1 − f)-initialization**
(Definition 8): writing `K` for the number of nodes that output an ID (the others output `none`,
i.e. are marked "uninitialized"),

1. every ID `k` output lies in `{1, …, K}`;
2. distinct nodes never output the same ID (so the IDs are exactly `1, …, K`);
3. `K ≥ (1 − f) n`, i.e. at most `f n` nodes are uninitialized.

Banasik, Dani, Hayes, full version §2.2, p.5 (PDF p.26), Definition 8: "Let f ∈ [0, 1]. The
(1 − f)-initialization problem seeks to number all but fn nodes in a single-hop radio network with
distinct IDs from 1 to (1 − f)n. The other fn nodes must be marked as “uninitialized.”"

**Formalization Note** `f n` need not be an integer, so "all but `f n`" is read as "all but at most
`f n`" and "IDs from 1 to (1 − f)n" as "the initialized nodes carry exactly the IDs `1, …, K` with
`K ≥ (1 − f) n`"; this is what the paper's proof of Theorem 3 delivers ("at most fn nodes remain
uninitialized", IDs handed out as the "next available ID"). For `f < 1/n` it is the published
`RadioInitBits.Protocol.Initialized` (every node gets an ID and the IDs are `1, …, n`). -/
def PartialInitialized (P : MProtocol) {n : ℕ} (f : ℝ) (ω : Fin n → Seed) : Prop :=
  (∀ (i : Fin n) (k : ℕ), P.out ω i = some k →
      1 ≤ k ∧ k ≤ (Finset.univ.filter fun j => (P.out ω j).isSome).card) ∧
  (∀ (i j : Fin n) (k : ℕ), P.out ω i = some k → P.out ω j = some k → i = j) ∧
  (1 - f) * n ≤ ((Finset.univ.filter fun j => (P.out ω j).isSome).card : ℝ)

end MProtocol

end Supplement

end RadioInitBits


