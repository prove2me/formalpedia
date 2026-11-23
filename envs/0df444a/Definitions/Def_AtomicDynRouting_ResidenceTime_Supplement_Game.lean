-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Game
-- name    : AtomicDynRouting_ResidenceTime_Supplement_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:31:30.572802+00:00
-- url     : https://prove2.me/theorems/4a9da1a9-1af1-4c7b-9ed3-c215b0b1f151
-- title:
--   §5, §5.1, pp. 12–13 — ADR games Γ1, Γ2, Γ3: selection rules (R1)–(R3), the run of a path profile, arrival times
-- statement:
--   An **ADR game** (§5) is played on a finite acyclic network $G=(V,E)$ with unit edge lengths and unit capacities and a single OD pair $(o,d)$. Each agent $i$ enters $G$ at the integer time $r_i$ (so $i\in\Delta_{r_i}$), with each $\Delta_r$ finite. The strategy set $\mathcal P$ is the set of $o$-$d$ paths; a **path profile** $p=(P_i)_{i\in\Delta}$ assigns one to each agent.
--
--   A **selection rule** decides which agent leaves a nonempty buffer at each integer time:
--
--   1. (R1), game $\Gamma_1$: the agent of highest priority in the global agent-priority list leaves;
--   2. (R2), game $\Gamma_2$: first-in-first-out (the agent who entered the buffer earliest leaves), a tie broken by the global priority;
--   3. (R3), game $\Gamma_3$: first-in-first-out, a tie between agents who entered the buffer at the same time broken by the priority of the incoming edges through which they reached the tail vertex, or, in the first buffer (agents entering $G$ together), by the original agent priority.
--
--   The global priority list is a complete ordering of the agents in which an earlier entrant always has higher priority; in $\Gamma_3$ every vertex $v\neq o$ carries a priority ordering of its incoming edges and each $\Delta_r$ an original priority ordering.
--
--   Given a profile, the run is determined time step by time step: at time $t$ every nonempty buffer releases its selected agent, who enters the buffer of his next edge at time $t+1$. The **arrival time** $t^v_j(p)$ of agent $j$ at a vertex $v$ is his entry time if $v=o$, one unit after he leaves the buffer of the edge of his route into $v$ otherwise, and $\infty$ if $v$ is not on his route.
--
--   **Formalization Note** The orders are relations `hp i j` ("$i$ before $j$"). Edge priorities are a strict total order `ep v` on all of $E$ for each $v$, and original priorities a strict total order `op` on all agents; only their restrictions to the incoming edges of $v$ and to each $\Delta_r$ are used, and every such family of orders is a restriction, so the same games are covered. The run is defined by recursion on time (`Game.state`), and the game run is also exported as data `Game.run p` of the base model, so that the base notions (inside, buffers, exit time) apply. Times are in $\mathbb N$, arrival times in $\mathbb N\cup\{\infty\}$.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), pp. 12–13 (PDF 13–14), §5 (game setting), §5.1 buffer selection rules (R1)–(R3), arrival times t^v_j(p)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Model

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

/-- The buffer selection rule of an ADR game (§5.1, pp. 12–13):
* `r1 hp` — game `Γ1`, rule (R1): among the agents in a buffer, the one of highest priority leaves;
* `r2 hp` — game `Γ2`, rule (R2): FIFO (the agent who entered the buffer earliest leaves), ties
  broken by the global priority;
* `r3 ep op` — game `Γ3`, rule (R3): FIFO, a tie between agents who entered the buffer at the same
  time broken by the priority `ep v` of the incoming edges to `v = tail e` through which they came,
  or, in the first buffer they enter (at the origin), by the original priority `op`.
`hp i j` (resp. `op i j`, `ep v e e'`) reads "`i` (resp. `e`) has higher priority than `j`
(resp. `e'`)". The admissible priorities are fixed by `Rule.Valid`. -/
inductive Rule (ι V E : Type) where
  | r1 (hp : ι → ι → Prop)
  | r2 (hp : ι → ι → Prop)
  | r3 (ep : V → E → E → Prop) (op : ι → ι → Prop)

/-- An instance of an ADR game (§5, p. 12): a network `N` with a single OD pair `(o, d)` used by
every agent, the entry time `entry i` of each agent `i` (agent `i ∈ Δ_{entry i}`), and the selection
rule. Edges have unit length and unit capacity (§5: "we always assume G is unit-capacitated"). -/
structure Game (ι V E : Type) where
  N : Network V E
  o : V
  d : V
  entry : ι → ℕ
  rule : Rule ι V E

variable {ι V E : Type}

namespace Game

variable (G : Game ι V E)

/-- The admissible priorities (§5.1, pp. 12–13).
* `Γ1`, `Γ2`: the global agent-priority list `hp` is a complete (strict total) ordering of all
  agents in which an agent entering `G` earlier always has a higher priority.
* `Γ3`: for every vertex `v` the edge priority `ep v` is a strict total order (only its restriction
  to the incoming edges of `v ≠ o` is ever used), and the original priority `op` is a strict total
  order of the agents (only its restriction to each `Δ_r` is ever used). Every family of orders of
  the incoming edges of each vertex, and every family of orders of the sets `Δ_r`, is such a
  restriction, so this quantifies over exactly the paper's priorities. -/
def RuleValid : Prop :=
  match G.rule with
  | .r1 hp => IsStrictTotalOrder ι hp ∧ ∀ i j, G.entry i < G.entry j → hp i j
  | .r2 hp => IsStrictTotalOrder ι hp ∧ ∀ i j, G.entry i < G.entry j → hp i j
  | .r3 ep op => (∀ v, IsStrictTotalOrder E (ep v)) ∧ IsStrictTotalOrder ι op

/-- The standing assumptions of §5 (p. 12) on the instance, besides finiteness and acyclicity of the
network, which are hypotheses of each theorem: each set `Δ_r` of agents entering at time `r` is
finite, and the priorities are admissible. -/
def Standing : Prop :=
  (∀ r : ℕ, {i | G.entry i = r}.Finite) ∧ G.RuleValid

/-- `P ∈ 𝒫` (§5.1, p. 13): `P` is an `o`-`d` path of the network (a nonempty edge list). -/
def IsODPath (P : List E) : Prop :=
  G.N.IsPathFrom G.o G.d P ∧ P ≠ []

/-- A path profile `p = (P_i)_{i ∈ Δ}`: every agent's route is an `o`-`d` path. -/
def IsProfile (p : ι → List E) : Prop :=
  ∀ i, G.IsODPath (p i)

end Game

/-- The state of an agent at an integer time in a game run: `pos` is the number of edges of his
route he has already traversed (so he is in the buffer of the edge of index `pos` of his route, or
at `d` once `pos` is the route length), and `since` is the time he entered his current buffer. -/
structure AState where
  pos : ℕ
  since : ℕ

namespace Game

variable (G : Game ι V E)

/-- `G.better p i a k b`: when agents `i` (state `a`) and `k` (state `b`) are in the same buffer,
the selection rule ranks `i` before `k`.
* (R1): `i` has higher global priority;
* (R2): `i` entered the buffer earlier, or at the same time with higher global priority;
* (R3): `i` entered the buffer earlier, or at the same time and either both are in the first buffer
  of their route (they entered `G` together) and `i` has the higher original priority, or both came
  from incoming edges `eᵢ`, `eₖ` (the previous edges of their routes) and `eᵢ` has the higher
  priority at their common head. -/
def better (p : ι → List E) (i : ι) (a : AState) (k : ι) (b : AState) : Prop :=
  match G.rule with
  | .r1 hp => hp i k
  | .r2 hp => a.since < b.since ∨ (a.since = b.since ∧ hp i k)
  | .r3 ep op => a.since < b.since ∨ (a.since = b.since ∧
      ((a.pos = 0 ∧ b.pos = 0 ∧ op i k) ∨
        (0 < a.pos ∧ 0 < b.pos ∧ ∃ ei ek, (p i)[a.pos - 1]? = some ei ∧
          (p k)[b.pos - 1]? = some ek ∧ ep (G.N.head ei) ei ek)))

/-- Agent `i` leaves his buffer at time `t` in the configuration `S`: he has entered `G`
(`entry i ≤ t`), is in the buffer of some edge `e` (the edge of index `pos` of his route), and the
selection rule ranks him before every other agent in the buffer of `e` at time `t`. With unit
capacity exactly this agent leaves (A2). -/
def selected (p : ι → List E) (t : ℕ) (S : ι → AState) (i : ι) : Prop :=
  G.entry i ≤ t ∧ ∃ e, (p i)[(S i).pos]? = some e ∧
    ∀ k, k ≠ i → G.entry k ≤ t → (p k)[(S k).pos]? = some e → G.better p i (S i) k (S k)

open Classical in
/-- The configuration of the game run under the profile `p` at every integer time (§2.4, §5.1): at
time `0` every agent is at the start of his route with buffer-entry time `entry i` (he enters the
buffer of his first edge when he enters `G`); from `t` to `t + 1` the selected agent of every buffer
moves to the next buffer, which he enters at `t + 1` (unit transit time and (A1)), and everybody else
stays. The run is thus uniquely determined by the profile, as §5.1 says. -/
noncomputable def state (p : ι → List E) : ℕ → ι → AState
  | 0 => fun i => ⟨0, G.entry i⟩
  | t + 1 => fun i =>
      if G.selected p t (state p t) i then ⟨(state p t i).pos + 1, t + 1⟩ else state p t i

open Classical in
/-- The time at which agent `i` leaves the buffer of the `j`-th edge (`0`-based) of his route under
the profile `p`, or `⊤` if he never does. -/
noncomputable def leave (p : ι → List E) (i : ι) (j : ℕ) : ℕ∞ :=
  if h : ∃ t, j < (G.state p (t + 1) i).pos then ((Nat.find h : ℕ) : ℕ∞) else ⊤

/-- The game run under the profile `p` as atomic dynamic routing data of the base model: entry
times, routes `p i`, common origin `o` and destination `d`, and the leaving times of the run. -/
noncomputable def run (p : ι → List E) : RunData ι E V where
  entry := G.entry
  route := p
  orig _ := G.o
  dest _ := G.d
  leave := G.leave p

/-- The vertex of index `k` of a path `P` from `o`: `o` for `k = 0`, the head of the `k`-th edge
otherwise (`none` past the end). -/
def vtxAt (P : List E) (k : ℕ) : Option V :=
  if k = 0 then some G.o else (P[k - 1]?).map G.N.head

/-- Agent `i`'s route under `p` passes the vertex `v`. -/
def passes (p : ι → List E) (i : ι) (v : V) : Prop :=
  ∃ k, k ≤ (p i).length ∧ G.vtxAt (p i) k = some v

/-- The time agent `i` reaches the vertex of index `k` of his route: his entry time for `o`, and one
unit after he leaves the buffer of the `k`-th edge otherwise. -/
noncomputable def reach (p : ι → List E) (i : ι) (k : ℕ) : ℕ∞ :=
  if k = 0 then (G.entry i : ℕ∞) else G.leave p i (k - 1) + 1

/-- `t^v_i(p)` (§5.1, p. 13): the arrival time of agent `i` at vertex `v` under the profile `p`,
`∞` (`⊤`) if `v` is not on his route (or he never gets there). -/
noncomputable def arrTime (p : ι → List E) (i : ι) (v : V) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : k ≤ (p i).length ∧ G.vtxAt (p i) k = some v), G.reach p i k

end Game

end AtomicDynRouting.ResidenceTime.Supplement


