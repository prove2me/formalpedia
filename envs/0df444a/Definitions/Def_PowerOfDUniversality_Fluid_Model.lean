-- Prove2me | Definitions.Def_PowerOfDUniversality_Fluid_Model
-- name    : PowerOfDUniversality_Fluid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:37.39716+00:00
-- url     : https://prove2.me/theorems/57235ffd-d2a0-433d-b6b8-c50273132b20
-- title:
--   The N-server system with buffer b: occupancy vector, ordered-position updates (3.2)/(3.3), JSQ, JSQ(d), MJSQ(n), JSQ(n, d), CJSQ(n), uniformized construction, S-coupling
-- statement:
--   This file sets up the many-server load-balancing model of Mukherjee, Borst, van Leeuwaarden and Whiting (§2.1 and §3).
--
--   **The system.** There are $N\ge 1$ identical single-server queues and one dispatcher. Tasks arrive as a Poisson process of rate $\lambda\ge 0$ and each requires an exponentially distributed amount of work with mean $1$, served at unit rate. Every server has a buffer of size $b\in\{1,2,\dots\}\cup\{\infty\}$, counting the task in service; a task sent to a server that already holds $b$ tasks is discarded (an *overflow event*), and $L(t)$ counts the overflow events in $[0,t]$.
--
--   **Occupancy vector.** The state is $\mathbf Q=(Q_1,Q_2,\dots)$, where $Q_i$ is the number of servers with at least $i$ tasks, together with the convention $Q_0\equiv N$ (and $Q_{b+1}\equiv 0$ for finite $b$). It is nonincreasing in $i$ and has finitely many nonzero entries. Arranging the servers in nondecreasing order of queue length, the $c$-th ordered server ($1\le c\le N$) holds
--   $$I(c)=\max\{i\ge 0: Q_i\ge N-c+1\}$$
--   tasks.
--
--   **Updates (3.2)–(3.3).** An arrival sent to the $c$-th ordered server raises $Q_{I(c)+1}$ by one if $I(c)<b$, and otherwise is discarded and raises $L$ by one. A departure from the $k$-th ordered server lowers $Q_{I(k)}$ by one if $I(k)\ge 1$, and changes nothing if that server is idle. A pair $(\mathbf Q,L)$ is an *ensemble of stacks*, and the ordering (3.1) of two ensembles $A,B$ is
--   $$\sum_{i=m}^{b}Q^A_i+L^A\le\sum_{i=m}^{b}Q^B_i+L^B\qquad\text{for every } m\ge 1 .$$
--
--   **Dispatch schemes.** A scheme selects, at each arrival, an ordered position in $\{1,\dots,N\}$:
--   1. JSQ always selects position $1$ (a shortest queue);
--   2. JSQ($d$), $1\le d\le N$, samples $d$ servers uniformly at random without replacement and selects the lowest ordered position among them; for $d=N$ this is JSQ;
--   3. MJSQ($n$) always selects position $n+1$;
--   4. CJSQ($n$) is the class of all schemes that, by some rule, select one of the positions $1,\dots,n+1$;
--   5. JSQ($n,d$) selects the JSQ($d$) choice if it lies in $\{1,\dots,n+1\}$, and otherwise a position chosen uniformly at random in $\{1,\dots,n+1\}$; it belongs to CJSQ($n$).
--
--   **Construction.** The system is built by uniformization: a Poisson clock of rate $\lambda+N$ whose events carry independent marks. An event is an arrival with probability $\lambda/(\lambda+N)$; otherwise it is a potential departure from a uniformly chosen ordered position (a dummy event if that server is idle), so each server completes service at rate $1$. The mark also carries independent uniform labels of the $N$ ordered positions, whose $d$ smallest define the random $d$-subset of JSQ($d$), and a uniform variable for the second step of JSQ($n,d$). The initial occupancy vector may be random and is independent of the clock and the marks. Systems driven by the same clock and marks, possibly under different schemes and from different initial states, are **S-coupled** (p. 13): they share arrival epochs and the departure clocks of the $k$-th ordered server.
--
--   **Derived processes.** For a scheme $\Pi$ the file defines $\mathbf Q^\Pi(t)$, $L^\Pi(t)$, the fluid-scaled state $\mathbf q(t)=\mathbf Q(t)/N$, the number of arrivals $A(t)$, the numbers $A_i(t)$ of arrivals assigned to a server with $i-1$ tasks and $D_i(t)$ of departures from a server with $i$ tasks (p. 17), the number $\Delta_{\Pi_1,\Pi_2}(t)$ of arrival epochs at which two S-coupled systems differ in decision (p. 14), and for JSQ the martingales
--   $$M_{A,i}(t)=A_i(t)-\lambda\int_0^t p_{i-1}(\mathbf Q(s))\,ds,\qquad M_{D,i}(t)=D_i(t)-\int_0^t\big(Q_i(s)-Q_{i+1}(s)\big)\,ds$$
--   of (4.8), where $p_{i-1}(\mathbf Q)=1$ if the shortest queue has exactly $i-1$ tasks and $0$ otherwise. Finally, a real process $X$ is stochastically smaller than $Y$, $X\le_{st}Y$, if there is a coupling $(X',Y')$ with the same laws such that almost surely $X'(t)\le Y'(t)$ for all $t\ge 0$.
--
--   These objects are the language of every statement of the mission.
--
--   **Formalization Note** Occupancy vectors are finitely supported functions `ℕ →₀ ℕ` with the paper's level index; coordinate `0` holds the convention $Q_0=N$. The buffer is `b : ℕ∞`. A scheme is a function of the event index, the current occupancy vector and the current mark; CJSQ($n$) members must also be measurable in the mark. Each mark is a real array: entry $0$ is the interarrival time ($\mathrm{Exp}(\lambda+N)$), entries $r\ge 1$ are independent Uniform$[0,1]$ variables (entry 1: arrival iff $(\lambda+N)u_1<\lambda$; entry 2: departure position; entry 3: JSQ($n,d$)'s uniform choice; entry $c+3$: label of position $c$). On the null event that infinitely many clock events fall in $[0,t]$ the state is frozen at its initial value. The martingales are defined from the counts, which agrees pathwise with the time-changed Poisson form (4.8).
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 4, 10–15, 17–18, §2.1, §3.1–3.3 ((3.1)–(3.3), Rule(n_A, n_B, k), S-coupling, Δ_{Π1,Π2}, JSQ(n, d)), (4.6), (4.8)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, *Universality of Power-of-d Load Balancing in
Many-Server Systems*, arXiv:1612.00723v2, §2.1 (p. 4) and §3 (pp. 10–15): the `N`-server system
with buffer `b`, its occupancy vector, the ordered-position update rules (3.2)/(3.3), the dispatch
schemes JSQ, JSQ(d), MJSQ(n), JSQ(n, d) and the class CJSQ(n), and the uniformized construction
of the system on a probability space.

**Index base.** Levels keep the paper's numbering: `Q i` is the paper's `Q_i` for `i ≥ 1`, and the
coordinate `Q 0` carries the paper's convention `Q₀ ≡ N`. Ordered positions are `c ∈ {1, …, N}`,
position `1` being a shortest queue. The buffer is `b : ℕ∞` with `b ≥ 1`; `b = ⊤` is an infinite
buffer, and for finite `b` the convention `Q_{b+1} ≡ 0` is the clause `Q i = 0` for `i > b`.
-/

/-- An **occupancy vector** of `N` servers with buffer `b` (p. 4): `Q i` is the number of servers
holding at least `i` tasks (`i ≥ 1`), with the convention `Q 0 = N`. It is nonincreasing in the
level, vanishes above the buffer `b`, and has finitely many nonzero levels (it is a finitely
supported function), since finitely many tasks are present. -/
def IsOccupancy (N : ℕ) (b : ℕ∞) (Q : ℕ →₀ ℕ) : Prop :=
  Q 0 = N ∧ Antitone ⇑Q ∧ ∀ i : ℕ, b < (i : ℕ∞) → Q i = 0

/-- The queue length of the `c`-th ordered server (servers in nondecreasing order of queue
length), `I(c) = max {i ≥ 0 : Q_i ≥ N − c + 1}` (proof of Proposition 3.1, p. 11), written
without natural-number subtraction as `N + 1 ≤ Q_i + c`. For an occupancy vector and
`1 ≤ c ≤ N`, every level in that set has `Q_i ≥ 1`, so the set lies in the support of `Q`, and it
contains `0` because `Q 0 = N`; the `Finset.sup` is therefore the paper's maximum. -/
def level (N : ℕ) (Q : ℕ →₀ ℕ) (c : ℕ) : ℕ :=
  (Q.support.filter (fun i => N + 1 ≤ Q i + c)).sup id

/-- An **ensemble of stacks** (p. 10): the occupancy vector `Q` together with the special stack
`L` of discarded items (the cumulative number of overflow events). -/
structure Ensemble where
  /-- the occupancy vector -/
  Q : ℕ →₀ ℕ
  /-- the number of discarded items -/
  L : ℕ

/-- Adding an item to the `c`-th ordered stack, (3.3) (p. 11): if `I(c) < b` then `Q_{I(c)+1}`
increases by one; otherwise the stack is full, the item is discarded and `L` increases by one. -/
noncomputable def addItem (N : ℕ) (b : ℕ∞) (c : ℕ) (x : Ensemble) : Ensemble :=
  if ((level N x.Q c : ℕ) : ℕ∞) < b then
    ⟨x.Q + Finsupp.single (level N x.Q c + 1) 1, x.L⟩
  else ⟨x.Q, x.L + 1⟩

/-- Removing an item from the `k`-th ordered stack, (3.2) (p. 11): if `I(k) ≥ 1` then `Q_{I(k)}`
decreases by one; otherwise the stack is empty and nothing changes. -/
noncomputable def removeItem (N : ℕ) (k : ℕ) (x : Ensemble) : Ensemble :=
  if 1 ≤ level N x.Q k then ⟨x.Q - Finsupp.single (level N x.Q k) 1, x.L⟩ else x

/-- The tail sum `∑_{i=m}^{b} Q_i` of an occupancy vector (the sum runs over the finitely many
nonzero levels `i ≥ m`; levels above `b` are zero). For `m > b` it is `0`. -/
def tailSum (Q : ℕ →₀ ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Q.support with m ≤ i, Q i

/-- The ordering (3.1) of two ensembles at every level: `∑_{i=m}^{b} Q^A_i + L^A ≤
∑_{i=m}^{b} Q^B_i + L^B` for every `m ≥ 1`. For `m > b` (finite `b`) the sums are empty and the
inequality reads `L^A ≤ L^B`. -/
def StackOrdered (x y : Ensemble) : Prop :=
  ∀ m : ℕ, 1 ≤ m → tailSum x.Q m + x.L ≤ tailSum y.Q m + y.L

/-- The `ℓ¹` distance `∑_{i=1}^{b} |Q_i − Q'_i|` of two occupancy vectors (as in (3.11)), summed
over the finitely many levels `i ≥ 1` where one of them is nonzero. -/
def occDist (Q Q' : ℕ →₀ ℕ) : ℕ :=
  ∑ i ∈ (Q.support ∪ Q'.support) with 1 ≤ i, Int.natAbs ((Q i : ℤ) - Q' i)

/-! ### Marks of the uniformized construction

The `j`-th event (`j ≥ 1`) of the uniformizing clock carries the real array `u = ξ j : ℕ → ℝ`:
`u 0` is the interarrival time before the event, and `u r` for `r ≥ 1` are independent
Uniform[0, 1] variables used as follows: `u 1` decides arrival versus departure, `u 2` the
departure position, `u 3` the uniform choice of JSQ(n, d), and `u (c + 3)` (`1 ≤ c ≤ N`) is the
random label of ordered position `c`, which defines the random `d`-subset. -/

/-- A uniform position in `{1, …, n}` from a Uniform[0, 1] variable `x`: `⌊n x⌋ + 1`, capped at
`n` (the cap only matters on the null event `x = 1`). -/
noncomputable def uniformPos (n : ℕ) (x : ℝ) : ℕ :=
  min (⌊(n : ℝ) * x⌋₊ + 1) n

/-- The event is an **arrival** iff `(λ + N) u₁ < λ`, which has probability `λ / (λ + N)` when
`u₁` is Uniform[0, 1]; otherwise it is a potential departure. -/
def IsArrival (N : ℕ) (lam : ℝ) (u : ℕ → ℝ) : Prop :=
  (lam + N) * u 1 < lam

/-- The rank of ordered position `c` among positions `1, …, N` by the labels `u (c + 3)`, ties
broken by the position index: the number of positions whose label precedes that of `c`. The ranks
of `1, …, N` are a permutation of `0, …, N − 1`. -/
noncomputable def labelRank (N : ℕ) (u : ℕ → ℝ) (c : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter
    (fun c' => u (c' + 3) < u (c + 3) ∨ (u (c' + 3) = u (c + 3) ∧ c' < c))).card

/-- The JSQ(d) choice: the **lowest ordered position** in the random `d`-subset
`{c : labelRank c < d}` of `{1, …, N}`. With i.i.d. continuous labels the subset is a uniformly
random `d`-subset (sampling **without** replacement), so this is "join a shortest queue among `d`
servers sampled uniformly at random", ties absorbed by the ordered-position convention. For
`1 ≤ d ≤ N` the subset is nonempty and the infimum is its minimum; `d = 0` is never used. For
`d = N` every position is sampled and the choice is position `1` (JSQ). -/
noncomputable def sampledMin (N d : ℕ) (u : ℕ → ℝ) : ℕ :=
  sInf {c : ℕ | 1 ≤ c ∧ c ≤ N ∧ labelRank N u c < d}

/-! ### Dispatch schemes -/

/-- A **dispatch scheme**: at the `j`-th event, given the current occupancy vector and the
event's mark, the ordered position `c` that an arrival is sent to. -/
abbrev Scheme : Type := ℕ → (ℕ →₀ ℕ) → (ℕ → ℝ) → ℕ

/-- The ordinary **JSQ** policy: always the first ordered position (a shortest queue). -/
def jsq : Scheme := fun _ _ _ => 1

/-- **MJSQ(n)** (p. 12): always the `(n + 1)`-th ordered position. -/
def mjsq (n : ℕ) : Scheme := fun _ _ _ => n + 1

/-- **JSQ(d)** (p. 4): the lowest ordered position among `d` positions sampled uniformly without
replacement. -/
noncomputable def jsqd (N d : ℕ) : Scheme := fun _ _ u => sampledMin N d u

/-- **JSQ(n, d)** (p. 15): take the JSQ(d) choice if it is one of the `n + 1` lowest ordered
positions; otherwise a position chosen uniformly at random among the first `n + 1`. -/
noncomputable def jsqnd (N n d : ℕ) : Scheme := fun _ _ u =>
  if sampledMin N d u ≤ n + 1 then sampledMin N d u else uniformPos (n + 1) (u 3)

/-- A scheme is **admissible** for `N` servers if it always selects a position in `{1, …, N}`. -/
def IsScheme (N : ℕ) (pol : Scheme) : Prop :=
  ∀ j Q u, 1 ≤ pol j Q u ∧ pol j Q u ≤ N

/-- The class **CJSQ(n)** (pp. 8, 12): schemes that assign every arriving task, by some rule, to
one of the `n + 1` lowest ordered servers. The rule may depend on the event index, the current
occupancy vector and the current event's mark (in a measurable way). -/
def IsCJSQ (n : ℕ) (pol : Scheme) : Prop :=
  (∀ j Q u, 1 ≤ pol j Q u ∧ pol j Q u ≤ n + 1) ∧ ∀ j Q, Measurable (pol j Q)

/-! ### The event recursion and the clock -/

/-- One event of the uniformized chain: an arrival is routed by the scheme (3.3); otherwise a
potential departure occurs at the uniformly chosen ordered position `uniformPos N (u 2)` (3.2),
a dummy event when that server is idle. -/
noncomputable def step (N : ℕ) (b : ℕ∞) (lam : ℝ) (pol : Scheme) (j : ℕ) (u : ℕ → ℝ)
    (x : Ensemble) : Ensemble := by
  classical
  exact if IsArrival N lam u then addItem N b (pol j x.Q u) x
    else removeItem N (uniformPos N (u 2)) x

/-- The state after the first `n` events, started from occupancy `Q₀` and no discarded tasks;
the `(n + 1)`-th event uses the mark `ξ (n + 1)`. -/
noncomputable def eventState (N : ℕ) (b : ℕ∞) (lam : ℝ) (pol : Scheme) (Q₀ : ℕ →₀ ℕ)
    (ξ : ℕ → ℕ → ℝ) : ℕ → Ensemble
  | 0 => ⟨Q₀, 0⟩
  | n + 1 => step N b lam pol (n + 1) (ξ (n + 1)) (eventState N b lam pol Q₀ ξ n)

/-- The number of clock events in `[0, t]`: the renewal count of the event epochs
`S_n = ξ 1 0 + ⋯ + ξ n 0`. On the null event where infinitely many epochs fall in `[0, t]` (the
count is `⊤`) it is set to `0`, i.e. the state is frozen at its initial value there. -/
noncomputable def eventCount (ξ : ℕ → ℕ → ℝ) (t : ℝ) : ℕ :=
  (BellWilliams2001.ThresholdPolicy.renewalCount
    (BellWilliams2001.ThresholdPolicy.partialSum (fun j => ξ j 0)) t).toNat

/-! ### The `N`-server system on a probability space -/

/-- The **`N`-server system** with buffer `b` and arrival rate `λ` on `(Ω, P)`, in uniformized
form: a Poisson clock of rate `λ + N` (i.i.d. `Exp(λ + N)` interarrival times `ξ j 0`), i.i.d.
Uniform[0, 1] marks `ξ j r` (`r ≥ 1`), all mutually independent, and an initial occupancy vector
`Q0`, independent of the clock and the marks. Each event is an arrival with probability
`λ / (λ + N)`, so arrivals form a Poisson process of rate `λ`; otherwise it is a departure from
a uniformly chosen ordered position, so each server completes service at rate `1` (unit-mean
exponential service). Systems driven by the same `ξ` are **S-coupled** (p. 13). -/
structure System {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ) (b : ℕ∞) (lam : ℝ) where
  /-- clock and marks: `ξ j 0` is the `j`-th interarrival time, `ξ j r` (`r ≥ 1`) the uniforms -/
  ξ : ℕ → ℕ → Ω → ℝ
  /-- the initial occupancy vector -/
  Q0 : Ω → ℕ →₀ ℕ
  measurable_ξ : ∀ j r, Measurable (ξ j r)
  iIndep_ξ : iIndepFun (fun p : ℕ × ℕ => ξ p.1 p.2) P
  law_clock : ∀ j, P.map (ξ j 0) = expMeasure (lam + N)
  law_mark : ∀ j r, 1 ≤ r → P.map (ξ j r) = volume.restrict (Set.Icc (0 : ℝ) 1)
  measurable_Q0 : ∀ i, Measurable (fun ω => Q0 ω i)
  isOccupancy_Q0 : ∀ ω, IsOccupancy N b (Q0 ω)
  indep_Q0 : IndepFun (fun ω i => Q0 ω i) (fun ω (p : ℕ × ℕ) => ξ p.1 p.2 ω) P

namespace System

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {b : ℕ∞} {lam : ℝ}

/-- The sample path of clock and marks at `ω`. -/
def marks (sys : System P N b lam) (ω : Ω) : ℕ → ℕ → ℝ := fun j r => sys.ξ j r ω

/-- The number of events in `[0, t]`. -/
noncomputable def count (sys : System P N b lam) (ω : Ω) (t : ℝ) : ℕ :=
  eventCount (sys.marks ω) t

/-- The state after `n` events under scheme `Π`. -/
noncomputable def stateSeq (sys : System P N b lam) (pol : Scheme) (ω : Ω) (n : ℕ) : Ensemble :=
  eventState N b lam pol (sys.Q0 ω) (sys.marks ω) n

/-- The occupancy vector `Q^Π(t)` at time `t` under scheme `Π`. -/
noncomputable def occ (sys : System P N b lam) (pol : Scheme) (ω : Ω) (t : ℝ) : ℕ →₀ ℕ :=
  (sys.stateSeq pol ω (sys.count ω t)).Q

/-- The cumulative number of overflow events `L^Π(t)` in `[0, t]` under scheme `Π`. -/
noncomputable def overflow (sys : System P N b lam) (pol : Scheme) (ω : Ω) (t : ℝ) : ℕ :=
  (sys.stateSeq pol ω (sys.count ω t)).L

/-- The fluid-scaled occupancy state `q(t) = Q(t)/N` (p. 5), coordinatewise; coordinate `0` is
`Q 0 / N = 1`. -/
noncomputable def fluid (sys : System P N b lam) (pol : Scheme) (ω : Ω) (t : ℝ) : ℕ → ℝ :=
  fun i => (sys.occ pol ω t i : ℝ) / N

/-- `A(t)`: the number of arrivals to the system in `[0, t]`. -/
noncomputable def arrivals (sys : System P N b lam) (ω : Ω) (t : ℝ) : ℕ := by
  classical
  exact ((Finset.range (sys.count ω t)).filter
    (fun k => IsArrival N lam (sys.marks ω (k + 1)))).card

/-- `A_i(t)` (p. 17): the number of arrivals in `[0, t]` that are assigned to a server with
`i − 1` tasks (`i ≥ 1`), i.e. whose chosen ordered position `c` has `I(c) + 1 = i`. For `i ≤ b`
these are exactly the arrivals that raise `Q_i`; for `i = b + 1` they are the discarded ones. -/
noncomputable def arrivalsTo (sys : System P N b lam) (pol : Scheme) (ω : Ω) (t : ℝ) (i : ℕ) :
    ℕ := by
  classical
  exact ((Finset.range (sys.count ω t)).filter (fun k =>
    IsArrival N lam (sys.marks ω (k + 1)) ∧
      level N (sys.stateSeq pol ω k).Q
        (pol (k + 1) (sys.stateSeq pol ω k).Q (sys.marks ω (k + 1))) + 1 = i)).card

/-- `D_i(t)` (p. 17): the number of departures in `[0, t]` from a server with `i` tasks
(`i ≥ 1`): potential departures at an ordered position `k` with `I(k) = i`. -/
noncomputable def departuresFrom (sys : System P N b lam) (pol : Scheme) (ω : Ω) (t : ℝ) (i : ℕ) :
    ℕ := by
  classical
  exact ((Finset.range (sys.count ω t)).filter (fun k =>
    ¬ IsArrival N lam (sys.marks ω (k + 1)) ∧
      level N (sys.stateSeq pol ω k).Q (uniformPos N (sys.marks ω (k + 1) 2)) = i)).card

/-- `Δ_{pol₁,pol₂}(t)` (p. 14) for two S-coupled systems `sys₁, sys₂` (the clock and marks of `sys₁`
are used; S-coupling means `sys₁.ξ = sys₂.ξ`): the number of arrival epochs in `[0, t]` at which
the two systems **differ in decision**, i.e. the chosen ordered positions differ. -/
noncomputable def diffDecisions (sys₁ sys₂ : System P N b lam) (pol₁ pol₂ : Scheme) (ω : Ω)
    (t : ℝ) : ℕ := by
  classical
  exact ((Finset.range (sys₁.count ω t)).filter (fun k =>
    IsArrival N lam (sys₁.marks ω (k + 1)) ∧
      pol₁ (k + 1) (sys₁.stateSeq pol₁ ω k).Q (sys₁.marks ω (k + 1)) ≠
        pol₂ (k + 1) (sys₂.stateSeq pol₂ ω k).Q (sys₁.marks ω (k + 1)))).card

end System

/-- `p^N_{i}(Q)` for the ordinary JSQ policy (p. 17): `1` if an arriving task joins a server
with exactly `i` tasks, i.e. the first ordered server has `I(1) = i` tasks (equivalently
`Q_1 = ⋯ = Q_i = N` and `Q_{i+1} < N`, the region `R_{i+1}` of (4.2)), and `0` otherwise. -/
noncomputable def jsqRoute (N : ℕ) (Q : ℕ →₀ ℕ) (i : ℕ) : ℝ :=
  if level N Q 1 = i then 1 else 0

namespace System

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {b : ℕ∞} {lam : ℝ}

/-- The arrival martingale of (4.8) for JSQ, written through the counts (equal pathwise to (4.8)):
`M_{A,i}(t) = A_i(t) − λ ∫_0^t p_{i−1}(Q(s)) ds` (`i ≥ 1`). The integrand is a bounded step
function of `s`, so the integral is a genuine Lebesgue integral. -/
noncomputable def jsqArrivalMart (sys : System P N b lam) (ω : Ω) (t : ℝ) (i : ℕ) : ℝ :=
  (sys.arrivalsTo jsq ω t i : ℝ) - lam * ∫ s in (0 : ℝ)..t, jsqRoute N (sys.occ jsq ω s) (i - 1)

/-- The departure martingale of (4.8) for JSQ, through the counts:
`M_{D,i}(t) = D_i(t) − ∫_0^t (Q_i(s) − Q_{i+1}(s)) ds` (`i ≥ 1`). -/
noncomputable def jsqDepartureMart (sys : System P N b lam) (ω : Ω) (t : ℝ) (i : ℕ) : ℝ :=
  (sys.departuresFrom jsq ω t i : ℝ) -
    ∫ s in (0 : ℝ)..t, ((sys.occ jsq ω s i : ℝ) - sys.occ jsq ω s (i + 1))

/-- `(1/N) ∑_{i=1}^{b} (|M_{A,i}(t)| + |M_{D,i}(t)|)` (Proposition 4.3), in `[0, ∞]`. -/
noncomputable def jsqMartNorm (sys : System P N b lam) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  ∑' i : ℕ, if 1 ≤ i ∧ (i : ℕ∞) ≤ b then
    ENNReal.ofReal ((|sys.jsqArrivalMart ω t i| + |sys.jsqDepartureMart ω t i|) / N) else 0

end System


/-- **Process-level stochastic order** `X ⩽_st Y` for real-valued processes indexed by `t ≥ 0`
on `(Ω₁, P₁)` and `(Ω₂, P₂)`: there are a probability space `(Ω', P')` and processes `X'`, `Y'`
on it with the laws of `X` and `Y` (laws of the paths on `[0, ∞)`, product σ-algebra) such that
almost surely `X'(t) ≤ Y'(t)` for all `t ≥ 0`. -/
def ProcLeSt {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (X : Ω₁ → ℝ → ℝ) (Y : Ω₂ → ℝ → ℝ) : Prop :=
  ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X' Y' : Ω' → ℝ → ℝ),
    IsProbabilityMeasure P' ∧
    IdentDistrib (fun ω (t : ℝ≥0) => X' ω t) (fun ω (t : ℝ≥0) => X ω t) P' P₁ ∧
    IdentDistrib (fun ω (t : ℝ≥0) => Y' ω t) (fun ω (t : ℝ≥0) => Y ω t) P' P₂ ∧
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t → X' ω t ≤ Y' ω t

end PowerOfDUniversality.Fluid


