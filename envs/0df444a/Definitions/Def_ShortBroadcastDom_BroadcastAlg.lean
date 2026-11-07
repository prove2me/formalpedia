-- Prove2me | Definitions.Def_ShortBroadcastDom_BroadcastAlg
-- name    : ShortBroadcastDom_BroadcastAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:33.38346+00:00
-- url     : https://prove2.me/theorems/b1c5acd5-6e0f-460c-ad0d-0cc5e8181a69
-- title:
--   Deterministic broadcast CONGEST algorithms, their execution, identifiers of $O(\log(n+1))$ bits and message bounds
-- statement:
--   In the **broadcast CONGEST** model the input graph $G$ is also the communication network. Vertices have distinct identifiers of $O(\log(n+1))$ bits, where $n=|V(G)|$, and computation proceeds in synchronous rounds; in each round a vertex sends **the same** message of $O(\log(n+1))$ bits to all its neighbours, however large its degree. Local computation and memory are unrestricted, and vertices need not know $n$.
--
--   A deterministic algorithm with local inputs in $I$ and outputs in $O$ is given by
--
--   1. a state space and an initial state $\mathrm{init}(\mathrm{id},i)$ computed from the vertex's identifier and its local input $i\in I$ only;
--   2. a message map: the bit string broadcast in the next round from the current state;
--   3. a transition: the new state from the current state and the multiset of messages received from the neighbours;
--   4. an output map from states to $O$.
--
--   Running it on $G$ for $T$ rounds gives every vertex a state; the output after exactly $T$ rounds is read off from it. Identifiers are **valid with exponent $k$** for an order $N$ if they are distinct and each is less than $(N+1)^k$; the run is **message-bounded with constant $c$** if every message broadcast in the first $T$ rounds has at most $c(\lfloor\log_2 N\rfloor+1)$ bits. A constant-round algorithm in the paper's sense is a single algorithm with a single round count $T$ that works for every graph of the class, with $k$ and $c$ independent of the graph.
--
--   The model is used by Theorem 6.1, Lemma 6.12, Theorem 6.13 and the goal, Theorem C.
--
--   **Formalization Note** The state type and all maps are arbitrary (unrestricted local computation; determinism is built in). Nothing about the graph enters the initial state, so no vertex knows $n$, its degree, an embedding or an orientation. Messages are received as a multiset, without port numbers or sender identities; this gives an algorithm no more information than port-numbered reception, so existence statements in this model are at least as strong (a sender can prepend its identifier at a cost of $O(\log(n+1))$ bits). Messages may be shorter than the bound ("empty messages are sent whenever a step has already finished"). Helper definitions read a local input $(\text{demand bit},\text{integer cost})$ as the demand set and the cost vector, and a rational output as the real coordinate $x_v$.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1, p.1 (PDF p.4); §4, p.15 (PDF p.18)

import Mathlib

namespace ShortBroadcastDom

/-- **A deterministic broadcast CONGEST algorithm** with local inputs in `I` and local outputs
in `O`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1, p.1 (PDF 4): "The algorithms work in the broadcast CONGEST model, where each vertex
sends the same O(log n)-bit message to all neighbors in a round, even when its degree is unbounded.
Vertices have distinct O(log n)-bit identifiers, and local computation is unrestricted." §4, p.15
(PDF 18): "in each synchronous round a vertex sends the same message of this size to every
neighbor. Local computation and memory are unrestricted. … The vertices need not know n."

The algorithm is one program run at every vertex:
1. `init id i` is the initial state of a vertex with identifier `id` and local input `i`;
2. in every round each vertex broadcasts the single message `msg s` (a bit string) computed from
   its current state `s`, the same message to all of its neighbours;
3. it then moves to `step s M`, where `M` is the multiset of messages received from its neighbours
   in that round;
4. `out s` is the vertex's output read from its state.

**Formalization Note** The state type is arbitrary and all four maps are arbitrary functions
(unrestricted local computation and memory; the map may be noncomputable). Determinism is built in.
The initial state sees only the vertex's identifier and its local input: no vertex knows `n`, its
degree, an embedding, an orientation or anything else about the graph unless it is part of the
local input. A vertex receives the *multiset* of its neighbours' messages, without port numbers or
sender identities; this gives an algorithm no more information than port-numbered reception, so an
existence statement over this model is at least as strong (a sender may prepend its identifier,
which costs `O(log(n+1))` bits). The size bound on messages is not part of the structure; see
`MsgBounded`. `State : Type` places `BroadcastAlg I O` in `Type 1`. -/
structure BroadcastAlg (I O : Type) : Type 1 where
  /-- The local state of one vertex. -/
  State : Type
  /-- The initial state from the vertex's identifier and its local input. -/
  init : ℕ → I → State
  /-- The message the vertex broadcasts in the next round. -/
  msg : State → List Bool
  /-- The state after receiving the multiset of the neighbours' messages. -/
  step : State → Multiset (List Bool) → State
  /-- The local output. -/
  out : State → O

/-- The execution of `A` on the graph `G` with identifiers `id` and local inputs `inp`:
`A.run G id inp t v` is the state of vertex `v` after `t` synchronous rounds. In round `t + 1`
every vertex `w` broadcasts `A.msg (state of w after t rounds)` and every vertex `v` receives the
multiset of these messages over its neighbours `w ∈ N_G(v)`. -/
def BroadcastAlg.run {I O : Type} (A : BroadcastAlg I O) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (id : V → ℕ) (inp : V → I) : ℕ → V → A.State
  | 0 => fun v => A.init (id v) (inp v)
  | t + 1 => fun v =>
      A.step (BroadcastAlg.run A G id inp t v)
        ((G.neighborFinset v).val.map fun w => A.msg (BroadcastAlg.run A G id inp t w))

/-- The output of vertex `v` after exactly `T` rounds. -/
def BroadcastAlg.output {I O : Type} (A : BroadcastAlg I O) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (id : V → ℕ) (inp : V → I) (T : ℕ) (v : V) : O :=
  A.out (A.run G id inp T v)

/-- The set of vertices whose Boolean output after `T` rounds is `true` (the returned vertex set,
e.g. the dominating set `D`). -/
def BroadcastAlg.outSet {I : Type} (A : BroadcastAlg I Bool) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (id : V → ℕ) (inp : V → I) (T : ℕ) : Finset V :=
  Finset.univ.filter fun v => A.output G id inp T v = true

/-- `ValidIds k N id`: the identifiers are distinct and each has `O(log(N + 1))` bits, namely
`id v < (N + 1)^k` (§4, p.15: "vertices have distinct identifiers of O(log(n + 1)) bits"). With
`N = n` the number of vertices this is the paper's assumption, `k` being the constant in the
`O(·)`. -/
def ValidIds {V : Type} (k N : ℕ) (id : V → ℕ) : Prop :=
  Function.Injective id ∧ ∀ v, id v < (N + 1) ^ k

/-- `MsgBounded A G id inp T c N`: during the first `T` rounds every message has at most
`c·(⌊log₂ N⌋ + 1)` bits, i.e. `O(log(N + 1))` bits with constant `c` (§4, p.15). Messages are
bit strings of variable length up to this bound ("empty messages are sent whenever a step has
already finished"). The message broadcast in round `t + 1` is `A.msg` of the state after `t`
rounds, so rounds `1, …, T` use the states at times `t < T`. -/
def MsgBounded {I O : Type} (A : BroadcastAlg I O) {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (id : V → ℕ) (inp : V → I) (T c N : ℕ) : Prop :=
  ∀ t < T, ∀ v, (A.msg (A.run G id inp t v)).length ≤ c * (Nat.log 2 N + 1)

/-- The demand set `R = {v : the demand bit of v is set}` of a local input `(demand bit, cost)`
(§4, p.15: "Every vertex knows whether it is a demand and knows its own cost"). -/
def demandsOf {V : Type} [Fintype V] (inp : V → Bool × ℕ) : Finset V :=
  Finset.univ.filter fun v => (inp v).1 = true

/-- The cost vector `c_v` (as a real number) of a local input `(demand bit, cost)`. -/
def costsOf {V : Type} (inp : V → Bool × ℕ) (v : V) : ℝ :=
  ((inp v).2 : ℝ)

/-- The rational output of vertex `v` after `T` rounds, read as a real number (the coordinate
`x_v` of a fractional vector computed by the algorithm). -/
noncomputable def BroadcastAlg.realOut {I : Type} (A : BroadcastAlg I ℚ) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (id : V → ℕ) (inp : V → I) (T : ℕ) (v : V) : ℝ :=
  ((A.output G id inp T v : ℚ) : ℝ)

end ShortBroadcastDom


