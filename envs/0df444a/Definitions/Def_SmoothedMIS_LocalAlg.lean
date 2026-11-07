-- Prove2me | Definitions.Def_SmoothedMIS_LocalAlg
-- name    : SmoothedMIS_LocalAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:46.859768+00:00
-- url     : https://prove2.me/theorems/fe57bda9-d42d-402b-81ff-36feb517f71c
-- title:
--   Randomized LOCAL algorithms, their execution, and private fair-coin tapes
-- statement:
--   A **randomized LOCAL algorithm** with global knowledge in $K$, inputs in $I$ and outputs in $O$ consists of a local state space, a message space (both arbitrary, so messages are unbounded and local computation is unrestricted), a round budget $T(k)$ depending only on the global knowledge $k$, an initial state $\mathrm{init}(k,\mathrm{ID}(v),x_v,\tau_v)$ computed from the knowledge, the node's own identifier, its own input and its own private random tape $\tau_v\in\{0,1\}^{\mathbb N}$, a message function and a state-update function.
--
--   It is executed on a communication graph $H$ in synchronous rounds: in each round every node sends one message to all its neighbours and updates its state from the multiset of messages it receives. After $T(k)$ rounds every node outputs a value computed from its state; for Boolean outputs, the **computed set** is the set of nodes that output true.
--
--   The **tape law** makes the tapes of all nodes independent sequences of independent fair coins.
--
--   This is the model in which Theorems 4.1 and 4.14 and Proposition 2.3 assert the existence of algorithms: a node does not see the graph, its degree, its neighbours' identifiers, the smoothing parameter, or which incident edges are random, and learns about the graph only through messages.
--
--   **Formalization Note** Broadcast with multiset reception is at most as strong as the paper's port-numbered LOCAL model, and simulates it after one round, since messages are unbounded and carry identifiers. A node knows the round number by counting in its state.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §1.5 "Distributed Computing Model", p.5 (PDF p.7)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SmoothedMIS

/-- **A randomized LOCAL algorithm** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis
for Distributed MIS* (manuscript, sha256 dc2131db…), §1.5 "Distributed Computing Model", p.5):
synchronous rounds, unbounded messages, unlimited local computation, a private source of
randomness per node, distinct identifiers, and global knowledge `K` (e.g. the number `n`).

* `rounds k` is the number of rounds the algorithm runs, a function of the global knowledge only;
* `init k id x τ` is a node's initial state from the knowledge `k`, its own identifier `id`, its
  own input `x` and its own private random tape `τ : ℕ → Bool`;
* in every round each node broadcasts `send s` to all its neighbours and then updates its state
  with `step s msgs`, where `msgs` is the multiset of messages received from its neighbours;
* `out s` is a node's output, read off its state after `rounds k` rounds.

**Formalization Note** A node does not see the graph, its degree, its neighbours' identifiers,
the vertex type, the smoothing parameter or which incident edges are random: it learns about the
graph only through messages. `State` and `Msg` are arbitrary types (unbounded messages,
unrestricted local computation). Broadcast with multiset reception is at most as powerful as the
paper's port-numbered model, and simulates it after one round of identifier exchange, since
messages are unbounded and carry identifiers. A node knows the round number by counting in its
state. -/
structure LocalAlg (K I O : Type) where
  /-- local state of a node -/
  State : Type
  /-- message type (unbounded) -/
  Msg : Type
  /-- round budget, from the global knowledge only -/
  rounds : K → ℕ
  /-- initial state: knowledge, own identifier, own input, own random tape -/
  init : K → ℕ → I → (ℕ → Bool) → State
  /-- the message a node broadcasts to all its neighbours in a round -/
  send : State → Msg
  /-- the state update from the multiset of the neighbours' messages -/
  step : State → Multiset Msg → State
  /-- the output of a node -/
  out : State → O

open Classical in
/-- The execution of `A` on the communication graph `H`: `A.run H k ids inp tape t v` is the
state of node `v` after `t` rounds, when node `v` has identifier `ids v`, input `inp v` and
random tape `tape v`, and every node knows `k`. -/
noncomputable def LocalAlg.run {K I O : Type} (A : LocalAlg K I O) {V : Type} [Fintype V]
    (H : SimpleGraph V) (k : K) (ids : V → ℕ) (inp : V → I) (tape : V → ℕ → Bool) :
    ℕ → V → A.State
  | 0 => fun v => A.init k (ids v) (inp v) (tape v)
  | t + 1 => fun v => A.step (LocalAlg.run A H k ids inp tape t v)
      ((Finset.univ.filter (H.Adj v)).val.map fun w => A.send (LocalAlg.run A H k ids inp tape t w))

/-- The output of node `v` after the algorithm's `A.rounds k` rounds. -/
noncomputable def LocalAlg.output {K I O : Type} (A : LocalAlg K I O) {V : Type} [Fintype V]
    (H : SimpleGraph V) (k : K) (ids : V → ℕ) (inp : V → I) (tape : V → ℕ → Bool) (v : V) : O :=
  A.out (A.run H k ids inp tape (A.rounds k) v)

/-- The set of nodes that output `true`, for an algorithm without inputs: the set the algorithm
computes (e.g. its MIS). -/
noncomputable def LocalAlg.outSet {K : Type} (A : LocalAlg K Unit Bool) {V : Type} [Fintype V]
    (H : SimpleGraph V) (k : K) (ids : V → ℕ) (tape : V → ℕ → Bool) : Set V :=
  {v | A.output H k ids (fun _ => ()) tape v = true}

/-- A fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

/-- **The private randomness** (§1.5, p.5: "a private source of randomness"): every node has an
independent infinite tape of fair coins, `tapeLaw V` is the product over the nodes of the
infinite product of fair coins on `ℕ → Bool`. -/
noncomputable def tapeLaw (V : Type) [Fintype V] : Measure (V → ℕ → Bool) :=
  Measure.pi fun _ => Measure.infinitePi fun _ : ℕ => fairCoin

end SmoothedMIS


