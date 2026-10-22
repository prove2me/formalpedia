-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Network_weightedThroughput
-- name    : OptimalQueuingComplexity_Network_weightedThroughput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:43:55.203894+00:00
-- url     : https://prove2.me/theorems/210d0d1c-0302-47a1-9e96-9d50fcd34530
-- title:
--   Network state, policies and the weighted throughput $J^\pi$
-- statement:
--   Fix an instance. The **state** of the closed network records how many customers of each class are waiting and which class (if any) each server is serving. A **policy** $\pi$ is deterministic and stationary. At each decision epoch it makes two kinds of choice from the current state: a routing choice $c' \in N(c)$ for a completing customer of class $c \in D$, and for every free server $s$ either to idle or to start a waiting customer of a class $c''$ with $\sigma(c'') = s$. Service is nonpreemptive. **Admissible** policies make only such choices.
--
--   The decision epochs are time $0$ and every service completion. At a completion of class $c$ at server $s$, the server is freed and the customer becomes class $c'$: the policy chooses $c'$ if $c \in D$, and $c'$ is drawn with probabilities $p_{cc'}$ if $c \in R$. The customer joins the waiting customers of class $c'$, and then every free server takes its sequencing decision. Service times are independent and exponential with mean $\mu(c)$ (rate $1/\mu(c)$). The next completion therefore occurs after an exponential time with the total rate $\Lambda$ of the busy servers, at server $s$ with probability $(1/\mu(c_s))/\Lambda$. A service with $\mu = 0$ is instantaneous: if one is in progress it completes at once, and simultaneous instantaneous completions are processed in increasing server index. If no server is busy, nothing happens any more.
--
--   With $a^\pi_c(t)$ the number of class-$c$ completions in $[0, t]$, the **weighted throughput** is
--   $$J^\pi = \limsup_{t \to \infty} \frac{1}{t} \sum_{c \in C} w(c)\, \mathbb{E}\big[a^\pi_c(t)\big].$$
--
--   **Formalization Note.** The process is built from its embedded chain of post-decision states. `epochLaw π k x` is the law of the $k$-th epoch time on the event that the post-decision state is $x$, and the holding time is a convolution with `expMeasure Λ` (or a Dirac mass at $0$). $\mathbb{E}[a^\pi_c(t)]$ is a sum in $[0, \infty]$ over epochs and states, and it is finite for well-formed instances. The $\limsup$ is taken in the extended reals, so it is always defined.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), pp. 294–295, Section 2 (routing and sequencing decisions, nonpreemptive policies, state, policy, weighted throughput J^π)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_Instance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OptimalQueuingComplexity.Network

/-- The state of the network (p. 295): "(a) how many customers of each class are present in the
system, and (b) the class of the customer (if any) being served at each server".
`waiting c` counts the class-`c` customers that are present and **not** in service;
`inService s` is the class of the customer served by `s`, or `none` if `s` is free. -/
structure NetState (I : Instance) where
  /-- number of waiting (not in service) class-`c` customers -/
  waiting : Fin I.nC → ℕ
  /-- class of the customer in service at server `s`, `none` if `s` is idle -/
  inService : Fin I.nS → Option (Fin I.nC)

/-- A (deterministic, stationary) policy (p. 295: "a rule for making decisions at service
completion times, as a function of the current state of the network").
* `route x c` is the next class chosen for a customer of class `c ∈ D` that has just completed
  service, when the rest of the network is in state `x` (the completing customer removed and its
  server freed).
* `start x s` is the sequencing decision of server `s` in state `x`: `none` = remain idle, or
  `some c` = start serving a waiting class-`c` customer. -/
structure Policy (I : Instance) where
  /-- routing decision for a class-`c` completion, `c ∈ D` -/
  route : NetState I → Fin I.nC → Fin I.nC
  /-- sequencing decision of server `s` -/
  start : NetState I → Fin I.nS → Option (Fin I.nC)

/-- Admissible policies: routing stays in `N(c)`, and a free server only starts a customer of a
class it serves, of which one is waiting. (The dynamics below treat any other sequencing choice
as idling, so this clause loses no behaviour.) -/
def Policy.Admissible {I : Instance} (π : Policy I) : Prop :=
  (∀ x c, I.inD c = true → I.next c (π.route x c) = true) ∧
    ∀ x s c, x.inService s = none → π.start x s = some c → I.server c = s ∧ 1 ≤ x.waiting c

/-- The sequencing decisions at a decision epoch, applied simultaneously (nonpreemptive: busy
servers keep their customer). A free server `s` with `start x s = some c`, `server c = s` and
`waiting c ≥ 1` starts serving one class-`c` customer; every other free server stays idle. Since
each class has a single server, the servers never compete for a customer. -/
def applyStarts {I : Instance} (π : Policy I) (x : NetState I) : NetState I where
  waiting c :=
    if x.inService (I.server c) = none ∧ π.start x (I.server c) = some c ∧ 1 ≤ x.waiting c then
      x.waiting c - 1
    else x.waiting c
  inService s :=
    match x.inService s with
    | some c => some c
    | none =>
      match π.start x s with
      | some c => if I.server c = s ∧ 1 ≤ x.waiting c then some c else none
      | none => none

/-- Server `s` completes its service: `s` becomes free (the customer leaves the server). -/
def freeServer {I : Instance} (x : NetState I) (s : Fin I.nS) : NetState I :=
  { x with inService := Function.update x.inService s none }

/-- A customer joins the waiting customers of class `c'`. -/
def joinClass {I : Instance} (x : NetState I) (c' : Fin I.nC) : NetState I :=
  { x with waiting := Function.update x.waiting c' (x.waiting c' + 1) }

/-- The initial state: `n_i(c)` waiting customers of each class, server `s ∈ S₀` serving
class `c_s`. -/
def initialState (I : Instance) : NetState I := ⟨I.init, I.busy0⟩

/-- The service rate `1/μ(c)` of server `s` if it serves class `c`, and `0` if it is idle. -/
noncomputable def serviceRate {I : Instance} (x : NetState I) (s : Fin I.nS) : ℝ :=
  match x.inService s with
  | some c => 1 / (I.mean c : ℝ)
  | none => 0

/-- The total service rate `Λ(x) = Σ_s serviceRate x s`. -/
noncomputable def totalRate {I : Instance} (x : NetState I) : ℝ :=
  ∑ s, serviceRate x s

/-- The lowest-indexed server that is serving a class of zero mean service time, if any. Such a
service completes instantaneously; simultaneous instantaneous completions are processed one at
a time in increasing server index. -/
def instantServer {I : Instance} (x : NetState I) : Option (Fin I.nS) :=
  (List.finRange I.nS).find? fun s =>
    match x.inService s with
    | some c => decide (I.mean c = 0)
    | none => false

/-- Probability that the next service completion happens at server `s`: if some busy server
serves a zero-mean class, the lowest-indexed such server completes (probability 1); otherwise
the independent exponential service times race, and server `s` completes first with probability
`serviceRate x s / Λ(x)`. When no server is busy all these probabilities are `0`: there are no
further completions. -/
noncomputable def serverProb {I : Instance} (x : NetState I) (s : Fin I.nS) : ℝ≥0∞ :=
  match instantServer x with
  | some s₀ => if s = s₀ then 1 else 0
  | none => ENNReal.ofReal (serviceRate x s / totalRate x)

/-- Law of the time from a decision epoch in state `x` to the next service completion: `0`
(Dirac mass) if a zero-mean service is in progress, otherwise exponential with rate `Λ(x)`
(the minimum of the independent exponential residual service times, by memorylessness). -/
noncomputable def holdingLaw {I : Instance} (x : NetState I) : Measure ℝ :=
  match instantServer x with
  | some _ => Measure.dirac 0
  | none => expMeasure (totalRate x)

/-- Routing probability of a customer of class `c` that completes service to class `c'`: for
`c ∈ D` the policy's choice `route x c` (probability 1), for `c ∈ R` the given `p_{cc'}`. -/
noncomputable def routeProb {I : Instance} (π : Policy I) (x : NetState I) (c c' : Fin I.nC) :
    ℝ≥0∞ :=
  if I.inD c = true then (if π.route x c = c' then 1 else 0) else ENNReal.ofReal (I.prob c c')

open Classical in
/-- Transition weight of the embedded chain of post-decision states: starting from the state `x`
reached after the decisions of an epoch, the next service completion is of class `c` and the
state after the decisions of the next epoch is `y`. The completing server `s` (serving class
`c`) is freed, the customer is routed to `c'` (by the policy if `c ∈ D`, at random if `c ∈ R`)
and joins the waiting customers of class `c'`, and then every free server takes its sequencing
decision (`applyStarts`). -/
noncomputable def transWeight {I : Instance} (π : Policy I) (x : NetState I) (c : Fin I.nC)
    (y : NetState I) : ℝ≥0∞ :=
  ∑ s, ∑ c', if x.inService s = some c ∧ applyStarts π (joinClass (freeServer x s) c') = y then
    serverProb x s * routeProb π (freeServer x s) c c' else 0

open Classical in
/-- `epochLaw π k x` is the law of the time `T_k` of the `k`-th decision epoch restricted to the
event that this epoch occurs and that the state after its decisions is `x` (a sub-probability
measure on `ℝ`). Epoch `0` is time `0`, where the free servers take their first sequencing
decisions; epoch `k + 1` is the `(k+1)`-th service completion, which occurs at
`T_{k+1} = T_k + H_k` with `H_k` distributed as `holdingLaw` of the current state,
independently of the past (`∗` is convolution of measures on `ℝ`). -/
noncomputable def epochLaw {I : Instance} (π : Policy I) : ℕ → NetState I → Measure ℝ
  | 0 => fun x => if x = applyStarts π (initialState I) then Measure.dirac 0 else 0
  | k + 1 => fun y =>
    Measure.sum fun x : NetState I => (∑ c, transWeight π x c y) • (epochLaw π k x ∗ holdingLaw x)

/-- `E[a_c^π(t)]`: the expected number of class-`c` service completions in `[0, t]` under the
policy `π` from the instance's initial state, as an extended nonnegative real. The `(k+1)`-th
completion happens at time `T_k + H_k` and is of class `c` with the weight `transWeight`. -/
noncomputable def expectedCompletions {I : Instance} (π : Policy I) (c : Fin I.nC) (t : ℝ) :
    ℝ≥0∞ :=
  ∑' k : ℕ, ∑' x : NetState I, ∑' y : NetState I,
    transWeight π x c y * (epochLaw π k x ∗ holdingLaw x) (Set.Iic t)

/-- `(1/t) Σ_{c ∈ C} w(c) E[a_c^π(t)]`. (For well-formed instances every `E[a_c^π(t)]` is
finite, so `toReal` loses nothing.) -/
noncomputable def throughputUpTo {I : Instance} (π : Policy I) (t : ℝ) : ℝ :=
  (1 / t) * ∑ c, (I.weight c : ℝ) * (expectedCompletions π c t).toReal

/-- The weighted throughput (p. 295)
`J^π = limsup_{t→∞} (1/t) Σ_{c ∈ C} w(c) E[a_c^π(t)]`,
with the `limsup` taken in the extended reals `EReal` (so it is always defined, and equals the
usual real `limsup` when the function is eventually bounded). -/
noncomputable def weightedThroughput {I : Instance} (π : Policy I) : EReal :=
  Filter.limsup (fun t : ℝ => ((throughputUpTo π t : ℝ) : EReal)) Filter.atTop

end OptimalQueuingComplexity.Network


