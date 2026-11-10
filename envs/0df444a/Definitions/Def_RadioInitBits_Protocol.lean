-- Prove2me | Definitions.Def_RadioInitBits_Protocol
-- name    : RadioInitBits_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:49.744596+00:00
-- url     : https://prove2.me/theorems/db391855-12e7-4c87-8d93-9154b8d42542
-- title:
--   Anonymous randomized radio protocols, their executions, bit counts and initialization
-- statement:
--   An **anonymous randomized protocol** for $n$ nodes is one piece of code that every node runs. It consists of:
--
--   1. a state space and an initial state $\mathrm{init}(s)$ computed from the node's private seed $s$;
--   2. for each round $r=0,1,2,\dots$ and state $x$, an action $\mathrm{act}(r,x)$: sleep, listen, or transmit one bit;
--   3. an update rule: after round $r$, a node in state $x$ that observed $o$ moves to state $\mathrm{update}(r,x,o)$;
--   4. a fixed number $R$ of rounds, and an output map giving each final state an ID $k\in\mathbb N$ or no ID.
--
--   The code contains no node identifier. Nodes differ only in their seeds and in what they hear. A family $P=(P_n)_{n\ge1}$ of protocols expresses that "all nodes know $n$".
--
--   The **execution** of $P_n$ on seeds $\omega=(\omega_1,\dots,\omega_n)$ starts with node $i$ in state $\mathrm{init}(\omega_i)$. In each round all nodes act simultaneously, each node observes the no-CD channel, and each node updates its state.
--
--   The **number of bits communicated** by node $i$ is the number of rounds $r<R$ in which it transmits or listens. With single-bit messages, each transmission is one bit sent and each listen is one bit received. A listen that hears silence also counts as one bit.
--
--   The execution **solves initialization** if every node outputs an ID in $\{1,\dots,n\}$ and the IDs are pairwise distinct, so they are exactly $1,\dots,n$.
--
--   These are the model, the cost measure and the success event of Theorem 5.
--
--   **Formalization Note** `Protocol` is a structure with an arbitrary `State : Type`. `config ω r i` is the state of node `i` before round `r`, `bits ω i` is the bit count, `out ω i` is the final output, and `Initialized ω` says the outputs are `some k` with `1 ≤ k ≤ n` and injective. The number of rounds is fixed in advance and does not depend on the seeds.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version §2.1–2.2, pp.4–5 (PDF pp.25–26), the bit complexity paragraph on p.5 and Definitions 7–8, p.5 (PDF p.26)

import Mathlib
import Definitions.Def_RadioInitBits_observe
import Definitions.Def_RadioInitBits_seedLaw

set_option autoImplicit false

namespace RadioInitBits

/-- An **anonymous randomized protocol** for a single-hop radio network with single-bit
messages and no collision detection. Every node runs the same code:

* `init s` is the node's initial state, computed from its private seed `s`;
* in round `r` (rounds are numbered `0, 1, 2, …`) a node in state `x` takes the action
  `act r x` (sleep, listen, or send one bit);
* after round `r` it moves to state `update r x o`, where `o` is what it observed in round `r`;
* the protocol runs for `rounds` rounds, after which a node in state `x` outputs `output x`
  (`some k`: the ID `k`; `none`: no ID).

D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version §2.1, pp.4–5 (PDF pp.25–26):
"all nodes are identical and execute the same protocol", "Communication occurs in synchronous
rounds, where all nodes have a shared clock and wake up at the same time".

**Formalization Note** No node index or identifier appears anywhere in a protocol: nodes differ
only by their seeds and by what they hear. The paper's "all nodes know n" is modelled by
families `P : ℕ → Protocol`, with `P n` run on `n` nodes. The number of rounds is fixed in
advance (it does not depend on the seeds). -/
structure Protocol where
  /-- The local state space of a node. -/
  State : Type
  /-- The initial state, computed from the node's private seed. -/
  init : Seed → State
  /-- The action taken in round `r` in state `x`. -/
  act : ℕ → State → Action
  /-- The state after round `r`, given the state before it and the observation in it. -/
  update : ℕ → State → Obs → State
  /-- The output (an ID, or `none`) of a node in final state `x`. -/
  output : State → Option ℕ
  /-- The number of rounds the protocol runs. -/
  rounds : ℕ

namespace Protocol

/-- The **execution** of `P` on `n` nodes with seeds `ω`: `P.config ω r i` is the state of node
`i` before round `r`. Node `i` starts in `P.init (ω i)`; in round `r` all nodes act
simultaneously, each node observes the no-CD channel (`observe`) applied to the actions of all
nodes, and updates its state. -/
def config (P : Protocol) {n : ℕ} (ω : Fin n → Seed) : ℕ → Fin n → P.State
  | 0 => fun i => P.init (ω i)
  | r + 1 => fun i =>
      P.update r (config P ω r i) (observe (fun j => P.act r (config P ω r j)) i)

/-- The **number of bits communicated** by node `i` in the execution of `P` with seeds `ω`: the
number of rounds `r < P.rounds` in which `i` transmits or listens.

Banasik, Dani, Hayes, full version §2.1, p.5 (PDF p.26): "The number of bits communicated by a
node is the sum of the number of bits it transmits and the number of bits it receives. When a node
listens and hears silence, we consider it as having received one bit." and "In the single-bit
setting, energy complexity is the same as bit complexity."

**Formalization Note** With single-bit messages a transmission is one bit and a listen is one
bit received (a bit, or silence); sleeping costs nothing. -/
def bits (P : Protocol) {n : ℕ} (ω : Fin n → Seed) (i : Fin n) : ℕ :=
  ((Finset.range P.rounds).filter fun r => P.act r (P.config ω r i) ≠ Action.sleep).card

/-- The output of node `i` at the end of the execution of `P` with seeds `ω`. -/
def out (P : Protocol) {n : ℕ} (ω : Fin n → Seed) (i : Fin n) : Option ℕ :=
  P.output (P.config ω P.rounds i)

/-- The execution of `P` on `n` nodes with seeds `ω` **solves initialization** (1-initialization):
every node outputs an ID in `{1, …, n}` and the IDs are pairwise distinct (so they are exactly
`1, …, n`).

Banasik, Dani, Hayes, full version §2.2, p.5 (PDF p.26), Definition 7: "The initialization problem
seeks to number all nodes in a single-hop radio network with distinct IDs from 1 to n."
Definition 8 with `f = 0` (1-initialization) is the same problem. -/
def Initialized (P : Protocol) {n : ℕ} (ω : Fin n → Seed) : Prop :=
  (∀ i, ∃ k : ℕ, P.out ω i = some k ∧ 1 ≤ k ∧ k ≤ n) ∧ Function.Injective (P.out ω)

end Protocol

end RadioInitBits


