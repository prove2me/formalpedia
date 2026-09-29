-- Prove2me | Definitions.Def_BCMPNetworks_Core_Dynamics
-- name    : BCMPNetworks_Core_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:40:18.940682+00:00
-- url     : https://prove2.me/theorems/6e2ffc2c-ad16-4b15-bb5c-bf7814448781
-- title:
--   BCMP network states, events and transition rates; global balance and equilibrium distributions
-- statement:
--   The **state** of a BCMP network is $S = (x_1,\dots,x_N)$ (§2.3). At a type-1 center $x_i$ is the list of the classes of its customers in FCFS order, the head being in service; at a type-2 or type-3 center $x_i = (m_{irl})_{r,l}$ counts the class-$r$ customers in stage $l$; at a type-4 center $x_i$ is the list of (class, stage) pairs in LCFS order, the head being the most recent arrival and the one in service. Let $n_{ir}$ be the number of class-$r$ customers at center $i$, $M(S/E_k) = \sum_{(i,r)\in E_k} n_{ir}$ and $M(S)$ the total number of customers. A configuration is **feasible** if each $x_i$ has the shape of its center's type and every closed subchain $E_k$ holds exactly $K_k$ customers; the state space is the set of feasible configurations.
--
--   A class-$s$ customer **entering** center $j$ is appended at the tail (type 1), added to stage $0$ (types 2, 3), or pushed on the head in stage $0$, preempting the current head (type 4). The transitions are the following events, each with its rate:
--
--   1. an external arrival entering $(j,s)$: rate $\lambda(M(S))\,q_{js}$ under (A), $\lambda_k(M(S/E_k))\,q_{js}$ with $E_k \ni (j,s)$ under (B);
--   2. at a nonempty type-1 center $i$ with head of class $r$: the head completes service at rate $\mu_i$ and is routed to $(j,s)$ with probability $p_{i,r;j,s}$ or leaves with probability $1-\sum p_{i,r;\cdot}$;
--   3. at a type-2 center: a class-$r$ customer in stage $l$ completes that stage at total rate $m_{irl}\mu_{irl}/n_i$, moving to stage $l+1$ with probability $a_{irl}$ or finishing and being routed with probability $b_{irl}$; at a type-3 center the same with rate $m_{irl}\mu_{irl}$;
--   4. at a nonempty type-4 center with head $(r,l)$: the head completes its stage at rate $\mu_{irl}$, moving to stage $l+1$ with probability $a_{irl}$, or finishing and being routed with probability $b_{irl}$.
--
--   The transition rate $q(S,S')$ is the sum of the rates of all events leading from $S$ to $S'$. A function $\pi$ on states satisfies the **global balance equations** (§3.1) when
--   $$\pi(S)\sum_{S'} q(S,S') = \sum_{S'} \pi(S')\,q(S',S) \quad\text{for every state } S,$$
--   and an **equilibrium distribution** is a nonnegative $\pi$ summing to $1$ that satisfies global balance.
--
--   These objects make the equilibrium question of the paper precise; every theorem of the mission is about this rate function.
--
--   **Formalization Note** Self-loops (e.g. a processor-sharing customer routed back to its own stage $0$) are kept in $q(S,S)$; they add the same term to both sides of global balance. Each state has finitely many successors and finitely many predecessors with nonzero rate, so the `tsum`s in the balance equations are finite sums. Events that are impossible in a state have rate $0$.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), pp. 250-251, Sections 2.1 and 2.3; p. 251, Section 3.1 (global balance equations)

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network

namespace BCMPNetworks.Core

/-- The local state `x_i` of one service center (§2.3, p. 251), for a center whose class-`r`
service time has `u r` Coxian stages.

* `fcfs l`: type 1; `l` lists the classes of the customers in FCFS order, the head is in
  service and an arrival joins at the end;
* `stages v`: types 2 and 3; `v r l` is the number of class-`r` customers in stage `l`;
* `lcfs l`: type 4; `l` lists the (class, stage) pairs in LCFS order, the head is the most
  recent arrival and is the one in service. -/
inductive LocalState (R : ℕ) (u : Fin R → ℕ+)
  | fcfs (l : List (Fin R))
  | stages (v : (r : Fin R) → Fin (u r) → ℕ)
  | lcfs (l : List (Σ r : Fin R, Fin (u r)))

namespace LocalState

variable {R : ℕ} {u : Fin R → ℕ+}

/-- `x` has the shape prescribed by the center type `t`. -/
def Fits : CenterType → LocalState R u → Prop
  | .fcfs, .fcfs _ => True
  | .ps, .stages _ => True
  | .is, .stages _ => True
  | .lcfs, .lcfs _ => True
  | _, _ => False

/-- `n_{ir}`: the number of class-`r` customers in the local state. -/
def count : LocalState R u → Fin R → ℕ
  | .fcfs l, r => l.count r
  | .stages v, r => ∑ k, v r k
  | .lcfs l, r => l.countP (fun x => decide (x.1 = r))

/-- `n_i`: the total number of customers in the local state. -/
def total (x : LocalState R u) : ℕ := ∑ r, x.count r

/-- A class-`s` customer enters the center: appended at the tail (FCFS), added to stage `0`
(PS, IS), or pushed on the head in stage `0`, preempting the current head (LCFS). -/
def enter : LocalState R u → Fin R → LocalState R u
  | .fcfs l, s => .fcfs (l ++ [s])
  | .stages v, s => .stages (fun r k => if r = s ∧ k.val = 0 then v r k + 1 else v r k)
  | .lcfs l, s => .lcfs (⟨s, ⟨0, (u s).pos⟩⟩ :: l)

end LocalState

namespace Network

variable {N R m : ℕ} (net : Network N R m)

/-- A configuration `S = (x_1, …, x_N)` of the whole network, before the feasibility
constraints are imposed. -/
abbrev Config := (i : Fin N) → LocalState R (net.u i)

/-- `M(S/E_k)`: the number of customers of subchain `k` in `S`. -/
def chainPop (S : net.Config) (k : Fin m) : ℕ :=
  ∑ i, ∑ r, if net.chain i r = k then (S i).count r else 0

/-- `M(S)`: the total number of customers in `S`. -/
def totalPop (S : net.Config) : ℕ := ∑ i, (S i).total

open Classical in
/-- A configuration is feasible when every local state has the shape of its center's type
and every closed subchain `k` holds exactly `K k` customers (§2.1, p. 250). -/
def Feasible (S : net.Config) : Prop :=
  (∀ i, (S i).Fits (net.type i)) ∧ (∀ k, net.IsClosedChain k → net.chainPop S k = net.K k)

/-- The state space of the network: the feasible configurations. -/
def State := {S : net.Config // net.Feasible S}

/-- A class-`s` customer enters center `j` of the configuration `S`. -/
def enterAt (S : net.Config) (j : Fin N) (s : Fin R) : net.Config :=
  Function.update S j ((S j).enter s)

/-- The routing destination of a customer after a service completion: `none` = leave the
network, `some (j, s)` = enter center `j` in class `s`. -/
def routeTo (S : net.Config) : Option (Fin N × Fin R) → net.Config
  | none => S
  | some (j, s) => net.enterAt S j s

/-- The probability of the routing destination `d` for a class-`r` customer completing
service at center `i`: `p_{i,r;j,s}` for `d = (j, s)`, and `1 - ∑_{j,s} p_{i,r;j,s}` for
leaving. -/
def routeProb (i : Fin N) (r : Fin R) : Option (Fin N × Fin R) → ℝ
  | none => 1 - ∑ j, ∑ s, net.P i r j s
  | some (j, s) => net.P i r j s

/-- The elementary events of the network. -/
inductive Event (N R : ℕ) (u : Fin N → Fin R → ℕ+)
  /-- an external arrival entering center `j` in class `s` -/
  | arrive (j : Fin N) (s : Fin R)
  /-- the head of a type-1 center `i` completes service and is routed to `d` -/
  | fcfsDone (i : Fin N) (d : Option (Fin N × Fin R))
  /-- a class-`r` customer in stage `l` at a type-2/3 center `i` moves to stage `l + 1` -/
  | stageNext (i : Fin N) (r : Fin R) (l : Fin (u i r))
  /-- a class-`r` customer in stage `l` at a type-2/3 center `i` completes service and is
  routed to `d` -/
  | stageDone (i : Fin N) (r : Fin R) (l : Fin (u i r)) (d : Option (Fin N × Fin R))
  /-- the head of a type-4 center `i` moves to its next stage -/
  | lcfsNext (i : Fin N)
  /-- the head of a type-4 center `i` completes service and is routed to `d` -/
  | lcfsDone (i : Fin N) (d : Option (Fin N × Fin R))

/-- The rate of the external arrival stream feeding the pair `(j, s)` in configuration
`S`: `λ(M(S)) q_{js}` for process (A), `λ_k(M(S/E_k)) q_{js}` with `k` the subchain of
`(j, s)` for process (B). -/
def arrivalRate (S : net.Config) (j : Fin N) (s : Fin R) : ℝ :=
  match net.arrival with
  | .total lam => lam (net.totalPop S) * net.q j s
  | .perChain lam => lam (net.chain j s) (net.chainPop S (net.chain j s)) * net.q j s

/-- Rate at which one particular class-`r` stage-`l` customer population `v r l` at a
type-2 or type-3 center completes stage `l`: `v_{irl} μ_{irl} / n_i` (processor sharing)
or `v_{irl} μ_{irl}` (infinite server). -/
noncomputable def stageRate (i : Fin N) (r : Fin R) (l : Fin (net.u i r))
    (v : (r : Fin R) → Fin (net.u i r) → ℕ) (n : ℕ) : ℝ :=
  match net.type i with
  | .ps => (v r l : ℝ) * net.μs i r l / n
  | .is => (v r l : ℝ) * net.μs i r l
  | _ => 0

/-- The rate of event `ev` in configuration `S` (zero when the event is impossible). -/
noncomputable def evRate (S : net.Config) : Event N R net.u → ℝ
  | .arrive j s => net.arrivalRate S j s
  | .fcfsDone i d =>
      match S i with
      | .fcfs (r :: _) => net.μ i * net.routeProb i r d
      | _ => 0
  | .stageNext i r l =>
      match S i with
      | .stages v => net.stageRate i r l v (S i).total * net.a i r l
      | _ => 0
  | .stageDone i r l d =>
      match S i with
      | .stages v => net.stageRate i r l v (S i).total * (1 - net.a i r l) * net.routeProb i r d
      | _ => 0
  | .lcfsNext i =>
      match S i with
      | .lcfs (x :: _) => net.μs i x.1 x.2 * net.a i x.1 x.2
      | _ => 0
  | .lcfsDone i d =>
      match S i with
      | .lcfs (x :: _) => net.μs i x.1 x.2 * (1 - net.a i x.1 x.2) * net.routeProb i x.1 d
      | _ => 0

/-- The configuration reached from `S` by event `ev` (`S` itself when the event is
impossible; such events have rate `0`). -/
def evTarget (S : net.Config) : Event N R net.u → net.Config
  | .arrive j s => net.enterAt S j s
  | .fcfsDone i d =>
      match S i with
      | .fcfs (_ :: rest) => net.routeTo (Function.update S i (.fcfs rest)) d
      | _ => S
  | .stageNext i r l =>
      match S i with
      | .stages v =>
          if l.val + 1 < (net.u i r : ℕ) then
            Function.update S i (.stages (fun r' k =>
              if r' = r ∧ k.val = l.val then v r' k - 1
              else if r' = r ∧ k.val = l.val + 1 then v r' k + 1 else v r' k))
          else S
      | _ => S
  | .stageDone i r l d =>
      match S i with
      | .stages v =>
          net.routeTo (Function.update S i (.stages (fun r' k =>
            if r' = r ∧ k.val = l.val then v r' k - 1 else v r' k))) d
      | _ => S
  | .lcfsNext i =>
      match S i with
      | .lcfs (x :: rest) =>
          if h : x.2.val + 1 < (net.u i x.1 : ℕ) then
            Function.update S i (.lcfs (⟨x.1, ⟨x.2.val + 1, h⟩⟩ :: rest))
          else S
      | _ => S
  | .lcfsDone i d =>
      match S i with
      | .lcfs (_ :: rest) => net.routeTo (Function.update S i (.lcfs rest)) d
      | _ => S

instance : Fintype (Event N R net.u) := by
  classical
  exact Fintype.ofEquiv
    ((Fin N × Fin R) ⊕ (Fin N × Option (Fin N × Fin R)) ⊕ (Σ i : Fin N, Σ r : Fin R, Fin (net.u i r)) ⊕
      ((Σ i : Fin N, Σ r : Fin R, Fin (net.u i r)) × Option (Fin N × Fin R)) ⊕
      Fin N ⊕ (Fin N × Option (Fin N × Fin R)))
    { toFun := fun
        | .inl (j, s) => .arrive j s
        | .inr (.inl (i, d)) => .fcfsDone i d
        | .inr (.inr (.inl ⟨i, r, l⟩)) => .stageNext i r l
        | .inr (.inr (.inr (.inl (⟨i, r, l⟩, d)))) => .stageDone i r l d
        | .inr (.inr (.inr (.inr (.inl i)))) => .lcfsNext i
        | .inr (.inr (.inr (.inr (.inr (i, d))))) => .lcfsDone i d
      invFun := fun
        | .arrive j s => .inl (j, s)
        | .fcfsDone i d => .inr (.inl (i, d))
        | .stageNext i r l => .inr (.inr (.inl ⟨i, r, l⟩))
        | .stageDone i r l d => .inr (.inr (.inr (.inl (⟨i, r, l⟩, d))))
        | .lcfsNext i => .inr (.inr (.inr (.inr (.inl i))))
        | .lcfsDone i d => .inr (.inr (.inr (.inr (.inr (i, d)))))
      left_inv := by
        intro x
        rcases x with ⟨j, s⟩ | ⟨i, d⟩ | ⟨i, r, l⟩ | ⟨⟨i, r, l⟩, d⟩ | i | ⟨i, d⟩ <;> rfl
      right_inv := by
        intro x
        cases x <;> rfl }

open Classical in
/-- The transition rate from state `S` to state `S'`: the sum of the rates of all events
leading from `S` to `S'`. Self-loops (`S' = S`) are kept; they contribute the same term to
both sides of the global balance equations. -/
noncomputable def rate (S S' : net.State) : ℝ :=
  ∑ ev : Event N R net.u, if net.evTarget S.1 ev = S'.1 then net.evRate S.1 ev else 0

end Network

/-- The global balance equations (§3.1, p. 251) of a function `π` for the transition rates
`q`: for every state `S_i`, `π(S_i) · (rate of flow out of S_i) = ∑_{S_j} π(S_j) · (rate of
flow from S_j to S_i)`. -/
def GlobalBalance {X : Type*} (π : X → ℝ) (q : X → X → ℝ) : Prop :=
  ∀ j, π j * ∑' k, q j k = ∑' k, π k * q k j

namespace Network

variable {N R m : ℕ} (net : Network N R m)

/-- An equilibrium distribution of the network: a probability distribution on the state
space satisfying the global balance equations. -/
def IsEquilibrium (Pr : net.State → ℝ) : Prop :=
  (∀ S, 0 ≤ Pr S) ∧ HasSum Pr 1 ∧ GlobalBalance Pr net.rate

end Network

end BCMPNetworks.Core


