-- Prove2me | Definitions.Def_PowerOfDUniversality_Diffusion_System
-- name    : PowerOfDUniversality_Diffusion_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:29.12331+00:00
-- url     : https://prove2.me/theorems/22453468-c628-4630-a8f6-ecdc3c46b601
-- title:
--   §2.1, (3.2)–(3.3), pp. 4, 7, 11 — the N-server system under JSQ(d(N)): occupancy states, updates, uniformized construction, diffusion scaling
-- statement:
--   This file defines the system of $N$ parallel single-server queues with one dispatcher studied by Mukherjee, Borst, van Leeuwaarden and Whiting, under the JSQ(d) scheme, together with its occupancy process and the diffusion scaling of §2.3.
--
--   **Model (p. 4).** Tasks arrive as a Poisson process of rate $\lambda\ge0$; each needs an exponential amount of work with mean one, served at unit rate. Each server has a buffer of size $b\in\{1,2,\dots\}\cup\{\infty\}$, counting the task in service; a task sent to a server that already holds $b$ tasks is discarded. On arrival the dispatcher samples $d$ servers ($1\le d\le N$) uniformly without replacement and sends the task to a server with the shortest queue among them; $d=N$ is the ordinary join-the-shortest-queue (JSQ) policy.
--
--   **Occupancy states.** The state is $Q=(Q_1,Q_2,\dots)$, where $Q_i$ is the number of servers with at least $i$ tasks, with the conventions $Q_0=N$ and $Q_i=0$ for $i>b$. An occupancy state is nonincreasing in $i$ and has finitely many nonzero entries. Arranging the servers in nondecreasing order of queue length, the $c$-th ordered server ($1\le c\le N$) has queue length
--   $$I(c)=\max\{i\ge 0:\ Q_i\ge N-c+1\}.$$
--
--   **Updates (3.2)–(3.3), p. 11.** A task routed to the $c$-th ordered server raises $Q_{I(c)+1}$ by one if $I(c)<b$ and is discarded otherwise. A departure from the $k$-th ordered server lowers $Q_{I(k)}$ by one if $I(k)\ge1$, and does nothing if that server is idle. Under JSQ(d) the task is routed to the smallest ordered position in a uniformly random $d$-subset of $\{1,\dots,N\}$.
--
--   **Construction of the process.** A Poisson clock of rate $\lambda+N$, with interarrival times $E_1,E_2,\dots$ i.i.d. exponential of rate $\lambda+N$, carries i.i.d. marks independent of the clock and of the random initial state $Q(0)$. A mark is an arrival with probability $\lambda/(\lambda+N)$, carrying a uniform $d$-subset of positions, and otherwise a departure at a position uniform on $\{1,\dots,N\}$. The occupancy process $Q^{d(N)}(t)$ is the state after the first $\Pi(t)$ marks, where $\Pi(t)=\sup\{n\ge0: E_1+\dots+E_n\le t\}$. Arrivals then occur at rate $\lambda$, each ordered position receives departure events at rate $1$, and every busy server completes work at rate $1$; this is the paper's model in law.
--
--   **Diffusion scaling (p. 7).**
--   $$\bar Q_1(t)=-\frac{N-Q_1(t)}{\sqrt N},\qquad \bar Q_i(t)=\frac{Q_i(t)}{\sqrt N},\quad i=2,\dots,b .$$
--   The diffusion-scaled occupancy process $\bar Q^{d(N)}$ is an $\ell_1$-valued path.
--
--   **Formalization Note** Levels and ordered positions use the paper's index base: `Q i` is $Q_i$ for $i\ge1$, `Q 0 = N` is part of an occupancy state, and position `c` is the $c$-th ordered server. `b : ℕ∞`, with `⊤` an infinite buffer. $I(c)$ is a supremum of natural numbers; for an occupancy state the set is finite and contains $0$. The condition $Q_i\ge N-c+1$ is written $N+1\le Q_i+c$, without natural-number subtraction. A system on $(\Omega,P)$ (`IsJSQdSystem`) requires measurable primitives, $1\le d\le N$, $\lambda\ge0$, every initial state an occupancy state, and the joint law of (initial state, interarrival times, marks) equal to the product of the initial law, the i.i.d. `expMeasure (λ + N)` law and the i.i.d. mark law. The interarrival time `E 0` and the mark `M 0` are never used. On the null set where the clock has infinitely many points in $[0,t]$ the count is read as $0$. In the diffusion-scaled state the unused coordinate $0$ is set to $0$.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 4, §2.1 (model, Q^{d(N)}(t)); p. 7, §2.3 (Q̄^{d(N)}); p. 11, proof of Proposition 3.1 (I_Π(c), updates (3.2), (3.3))

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, §2.1 (p. 4), §2.3 (p. 7) and the
update rules (3.2)–(3.3) of §3 (p. 11): the system of `N` parallel single-server queues under the
JSQ(d(N)) scheme, its occupancy process and its diffusion scaling.

**Index conventions.** Occupancy levels use the paper's index base: `Q i` is `Q_i`, the number of
servers with at least `i` tasks, for `i ≥ 1`; the entry `Q 0` is the paper's convention `Q_0 ≡ N`.
Ordered positions also use the paper's base: position `c ∈ {1, …, N}` is the `c`-th server when the
servers are arranged in nondecreasing order of their queue lengths. The buffer size is `b ∈ ℕ∞`
(`b = ⊤` is an infinite buffer).

**Construction of the process (uniformization).** A Poisson clock of rate `λ + N` carries i.i.d.
marks, independent of the clock and of the initial state. A mark is an *arrival* with probability
`λ/(λ + N)`, together with a uniformly random `d`-subset of the positions `{1, …, N}`; otherwise it
is a *departure at ordered position `k`*, with `k` uniform on `{1, …, N}`. The state at time `t` is
the event recursion applied to the first `Π(t)` marks, `Π(t)` the number of clock points in
`[0, t]`. This has the law of the paper's model: arrivals occur at rate `λ` and are routed to the
lowest ordered position among `d` servers sampled without replacement (a server with the shortest
queue among them; ties are absorbed by the ordering convention); each ordered position `k` sees
departure events at rate `1`, which remove a task from the `k`-th ordered server when it is busy
and are dummy events when it is idle, so that every busy server completes work at rate `1`, as
unit-mean exponential service at unit rate requires.
-/

/-- An **occupancy state** of `N` servers with buffer `b` (p. 4): `Q 0 = N` (the convention
`Q_0 ≡ N`), the entries are nonincreasing in the level, they vanish above the buffer size (`Q_i = 0`
for `i > b`, the convention `Q_{b+1} ≡ 0`), and only finitely many are nonzero (finitely many
tasks; this matters only for `b = ∞`). -/
def IsOccupancy (N : ℕ) (b : ℕ∞) (Q : ℕ → ℕ) : Prop :=
  Q 0 = N ∧ Antitone Q ∧ (∀ i : ℕ, b < (i : ℕ∞) → Q i = 0) ∧ ∃ M : ℕ, ∀ i, M ≤ i → Q i = 0

/-- The queue length of the `c`-th ordered server, `I(c) = max {i ≥ 0 : Q_i ≥ N − c + 1}` for
`c ∈ {1, …, N}` (proof of Proposition 3.1, p. 11). The condition `N + 1 ≤ Q_i + c` is
`Q_i ≥ N − c + 1` without natural-number subtraction. For an occupancy state the set contains `0`
(as `Q 0 = N`) and is finite, so the supremum is its maximum; on a set that is not bounded above the
value would be `0`, which no occupancy state produces. -/
noncomputable def orderedLen (N : ℕ) (Q : ℕ → ℕ) (c : ℕ) : ℕ :=
  sSup {i : ℕ | N + 1 ≤ Q i + c}

/-- Update (3.3) (p. 11): a task routed to the `c`-th ordered server raises `Q_{I(c)+1}` by one if
`I(c) < b`; otherwise the task is discarded (an overflow event) and the state is unchanged. -/
noncomputable def arrive (b : ℕ∞) (N : ℕ) (Q : ℕ → ℕ) (c : ℕ) : ℕ → ℕ :=
  if ((orderedLen N Q c : ℕ) : ℕ∞) < b then
    Function.update Q (orderedLen N Q c + 1) (Q (orderedLen N Q c + 1) + 1)
  else Q

/-- Update (3.2) (p. 11): a departure from the `k`-th ordered server lowers `Q_{I(k)}` by one if
`I(k) ≥ 1`; otherwise (the server is idle) nothing happens. In an occupancy state
`Q_{I(k)} ≥ N − k + 1 ≥ 1` when `I(k) ≥ 1`, so the natural-number subtraction never truncates. -/
noncomputable def depart (N : ℕ) (Q : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  if 1 ≤ orderedLen N Q k then
    Function.update Q (orderedLen N Q k) (Q (orderedLen N Q k) - 1)
  else Q

/-- A mark of the uniformized clock: whether the event is an arrival, the set of ordered positions
sampled by an arrival, and the ordered position of a departure. -/
structure Mark where
  /-- `true` for an arrival event, `false` for a departure event. -/
  arrival : Bool
  /-- For an arrival: the sampled ordered positions, a `d`-subset of `{1, …, N}`. -/
  sample : Finset ℕ
  /-- For a departure: the ordered position `k ∈ {1, …, N}` of the server. -/
  pos : ℕ

/-- Marks carry the discrete σ-algebra. -/
instance : MeasurableSpace Mark := ⊤

/-- The **JSQ(d) dispatch rule** (p. 4): the arriving task joins the lowest ordered position among
the sampled ones, i.e. a server with the shortest queue among the `d` sampled servers. With
`d = N` every position is sampled and the rule is JSQ (position `1`). The sample is never empty
under `markLaw` with `d ≥ 1`; on an empty set the value would be `0`. -/
noncomputable def jsqdPosition (m : Mark) : ℕ :=
  sInf (m.sample : Set ℕ)

/-- One event of the uniformized chain under JSQ(d): an arrival is routed by `jsqdPosition`
and updates the state by (3.3); a departure at position `k` updates it by (3.2). -/
noncomputable def step (b : ℕ∞) (N : ℕ) (Q : ℕ → ℕ) (m : Mark) : ℕ → ℕ :=
  if m.arrival then arrive b N Q (jsqdPosition m) else depart N Q m.pos

/-- The state after the first `n` events, starting from `Q₀`; event number `n ≥ 1` uses the mark
`M n` (the mark `M 0` is never used). -/
noncomputable def stateAfter (b : ℕ∞) (N : ℕ) (Q₀ : ℕ → ℕ) (M : ℕ → Mark) : ℕ → ℕ → ℕ
  | 0 => Q₀
  | n + 1 => step b N (stateAfter b N Q₀ M n) (M (n + 1))

/-- The **occupancy process** `Q^{d(N)}(t)` (p. 4): the state after the `Π(t)` events of the clock
in `[0, t]`, where the clock has interarrival times `E 1, E 2, …` and
`Π(t) = renewalCount (partialSum E) t = sup {n ≥ 0 : E 1 + ⋯ + E n ≤ t}`. For i.i.d. exponential
interarrival times `Π(t)` is almost surely finite; on the null set where it is infinite, `toNat`
gives `0` and the state is the initial one. -/
noncomputable def occupancyProcess (b : ℕ∞) (N : ℕ) (Q₀ : ℕ → ℕ) (E : ℕ → ℝ) (M : ℕ → Mark)
    (t : ℝ) : ℕ → ℕ :=
  stateAfter b N Q₀ M (BellWilliams2001.ThresholdPolicy.renewalCount
    (BellWilliams2001.ThresholdPolicy.partialSum E) t).toNat

/-- The **law of a mark** for `N` servers, JSQ(d) with `d` samples and arrival rate `λ`:
with probability `λ/(λ + N)` the event is an arrival whose sample is uniform over the `d`-subsets of
`{1, …, N}` (sampling without replacement); with probability `N/(λ + N)` it is a departure whose
position is uniform on `{1, …, N}`. The unused field is fixed (`pos = 1` for an arrival, `sample = ∅`
for a departure). It is a probability measure when `N ≥ 1`, `λ ≥ 0` and `d ≤ N`. -/
noncomputable def markLaw (N d : ℕ) (lam : ℝ) : Measure Mark :=
  (∑ S ∈ (Finset.Icc 1 N).powersetCard d,
      ENNReal.ofReal (lam / (lam + N) / (N.choose d)) • Measure.dirac (⟨true, S, 1⟩ : Mark)) +
  ∑ k ∈ Finset.Icc 1 N, ENNReal.ofReal (1 / (lam + N)) • Measure.dirac (⟨false, ∅, k⟩ : Mark)

/-- **The JSQ(d) system with `N` servers on a probability space `(Ω, P)`** (§2.1, p. 4): its
primitives are a random initial occupancy state `Q₀`, the interarrival times `E` of a Poisson clock
of rate `λ + N`, and the marks `M`. The conditions are:
1. `P` is a probability measure, `1 ≤ d ≤ N` (so `N ≥ 1`) and `λ ≥ 0`;
2. the primitives are measurable;
3. every initial state is an occupancy state with buffer `b`;
4. the joint law of `(Q₀, E, M)` is the product of the law of `Q₀`, the i.i.d. `Exp(λ + N)` law of
   the interarrival times, and the i.i.d. law `markLaw N d λ` of the marks: the clock, the marks and
   the initial state are independent. -/
structure IsJSQdSystem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N d : ℕ) (lam : ℝ)
    (b : ℕ∞) (Q₀ : Ω → ℕ → ℕ) (E : Ω → ℕ → ℝ) (M : Ω → ℕ → Mark) : Prop where
  isProb : IsProbabilityMeasure P
  one_le_d : 1 ≤ d
  d_le_N : d ≤ N
  lam_nonneg : 0 ≤ lam
  meas_init : Measurable Q₀
  meas_clock : Measurable E
  meas_marks : Measurable M
  init_occ : ∀ ω, IsOccupancy N b (Q₀ ω)
  law : P.map (fun ω => (Q₀ ω, E ω, M ω)) =
    (P.map Q₀).prod ((Measure.infinitePi fun _ : ℕ => ProbabilityTheory.expMeasure (lam + N)).prod
      (Measure.infinitePi fun _ : ℕ => markLaw N d lam))

/-- The **diffusion-scaled state** (p. 7): `Q̄_1 = −(N − Q_1)/√N` and `Q̄_i = Q_i/√N` for
`i = 2, …, b`, with the paper's index base; the unused coordinate `0` is set to `0`. Coordinates
above the buffer size are `0` because `Q_i = 0` there. -/
noncomputable def diffScaled (N : ℕ) (Q : ℕ → ℕ) : ℕ → ℝ := fun i =>
  if i = 0 then 0
  else if i = 1 then -(((N : ℝ) - (Q 1 : ℝ)) / Real.sqrt N)
  else (Q i : ℝ) / Real.sqrt N

/-- The **diffusion-scaled occupancy process** `Q̄^{d(N)}(t)` (p. 7) of the JSQ(d) system with
primitives `(Q₀, E, M)`, as an `ℓ¹`-valued path. -/
noncomputable def diffusionProcess (b : ℕ∞) (N : ℕ) (Q₀ : ℕ → ℕ) (E : ℕ → ℝ) (M : ℕ → Mark)
    (t : ℝ) : ℕ → ℝ :=
  diffScaled N (occupancyProcess b N Q₀ E M t)

end PowerOfDUniversality.Diffusion


