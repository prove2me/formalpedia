-- Prove2me | Definitions.Def_SRPTManyServer_Collapse_Model
-- name    : SRPTManyServer_Collapse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:08.051973+00:00
-- url     : https://prove2.me/theorems/95b37064-dea5-4a56-89ea-a4a6ed83648f
-- title:
--   §2, pp. 5–9 — M/GI/s+GI queue under SRPT with abandonment: schedules, outcomes, waiting times, the coupled loss system, long-run averages
-- statement:
--   This file sets up the model of Dong and Ibrahim: the many-server queue with impatient customers operated under **shortest remaining processing time first** (SRPT), the coupled loss system used in its analysis, and the probability model of the overloaded many-server sequence.
--
--   **Sample paths.** Customers are numbered $n = 0, 1, 2, \dots$ in order of arrival. A sample path consists of the arrival times $A_n$, service times $S_n$ and patience times $T_n$. A path is *admissible* when $A_n$ is strictly increasing, $A_0 \ge 0$, $A_n \to \infty$, and every $S_n$ and $T_n$ is strictly positive.
--
--   **Schedules.** A schedule is a family $\delta_n(t) \in \{0,1\}$, with $\delta_n(t) = 1$ meaning that customer $n$ occupies a server at time $t$. From it one reads off
--   $$\text{served}_n(t) = \int_{A_n}^t \delta_n(u)\,du,\qquad R_n(t) = S_n - \text{served}_n(t),\qquad Q_n(t) = (t - A_n) - \text{served}_n(t),$$
--   the service received, the remaining processing time, and the cumulative time spent in queue. Customer $n$ is *present* at time $t$ if $A_n \le t$, $R_n(t) > 0$ and $Q_n(t) < T_n$: she has arrived, is not finished, and has not yet abandoned. A schedule is an **SRPT schedule with $s$ servers** if
--
--   1. each $\delta_n$ is a measurable $\{0,1\}$-valued function, and only present customers are served;
--   2. it is non-idling: at every $t$ the number of customers in service equals $\min(s, \#\{\text{present customers}\})$;
--   3. every customer in service has remaining processing time at most that of every present customer who is waiting (ties are broken arbitrarily).
--
--   Customer $n$ is *served* ($\mathrm{Serv}$) if $S_n \le \text{served}_n(t)$ for some $t \ge A_n$, and *abandons* ($\mathrm{Ab}$) otherwise. Her **waiting time** $W_n$ is the Lebesgue measure of the set of times at which she is present but not in service; for an abandoning customer this is $T_n$. $N_O(t)$ is the number of customers served by time $t$, and the completed work is the sum of $S_n$ over them.
--
--   **The coupled loss system** $L$ (§3.1) has the same customers and $s$ servers and no waiting room. Class 1 consists of the customers with $S_n \le \tau$. A class 1 customer is accepted if, at her arrival, fewer than $s$ earlier accepted class 1 customers are still in service; she is then served without interruption and leaves at $A_n + S_n$. Class 2 customers never block class 1, because class 1 preempts class 2. $N_{L,1}(t)$ is the number of class 1 customers served in $L$ by time $t$.
--
--   **Probability model.** On a probability space $(\Omega, P)$ live i.i.d. $\mathrm{Exp}(1)$ variables $E_n$, i.i.d. service times $S_n \sim \nu_S$ and i.i.d. patience times $T_n \sim \nu_T$, all mutually independent. System $s$ has $s$ servers and Poisson arrivals of rate $\lambda_s = \rho\mu s$:
--   $$A_n = \frac{E_0 + \cdots + E_n}{\rho\mu s}.$$
--   The **standing assumptions** (§2.1–§2.2) are: $\nu_S$ and $\nu_T$ are probability laws on $[0,\infty)$ with densities ($g$ for the service law), means $\int x\,d\nu_S = 1/\mu$ and $\int x\,d\nu_T = 1/\theta$ with $\mu, \theta > 0$, traffic intensity $\rho > 1$, and the threshold $\tau$ satisfies (1):
--   $$\mathbb E[S\,\mathbf 1(S \le \tau)] = \frac{s_\lambda}{\lambda} = \frac{1}{\rho\mu}.$$
--
--   **Long-run averages.** For a class of customers $c$ and a quantity $f$, $\mathrm{avg}_N$ is the average of $f_n$ over the customers $n < N$ in $c$ (zero if there are none). A number $v$ is the *long-run average* of $f$ over $c$ if $\mathrm{avg}_N \to v$ as $N \to \infty$, $P$-almost surely. This is how the paper's steady-state quantities for a tagged customer are read.
--
--   **Formalization Note** The SRPT discipline is encoded relationally, as "the $s$ present customers with the shortest remaining work are in service". The page describes preemption at arrival epochs; the relational form also fixes who takes a server freed by a departure. Admissibility requires $S_n, T_n > 0$; under the standing assumptions this holds almost surely, and it excludes a customer with zero patience who would be refused even an idle server. Counts are `Set.ncard`, which is finite on admissible paths. All systems share one probability space, with arrivals scaled by $\lambda_s = \rho\mu s$; only the law of each system matters. The index $s \in \mathbb N$ replaces the paper's $\lambda$, with $s_\lambda = \lambda/(\rho\mu)$.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, pp. 5–9, §2.1, §2.2 (eq. (1)), §3.1 (eq. (2)), §3.2

import Mathlib

namespace SRPTManyServer.Collapse

open MeasureTheory ProbabilityTheory Filter Topology

/-!
Dong & Ibrahim, *On the SRPT scheduling discipline in many-server queues with impatient
customers*, arXiv:2102.05789v1: the M/GI/s+GI queue under SRPT (§2.1, p. 5), the overloaded
many-server scaling and the threshold τ of (1) (§2.2, p. 6), the coupled two-class preemptive
priority loss system and the throughputs (2) (§3.1, pp. 7–8), and the tagged-customer quantities
of §3.2 (p. 9), read as customer long-run averages.

Customers are indexed `0, 1, 2, …` in order of arrival.
-/

/-- One sample path of the primitives: arrival time `A n`, service time `S n` and patience time
`T n` of the `n`-th arriving customer (index base 0). -/
structure Stream where
  A : ℕ → ℝ
  S : ℕ → ℝ
  T : ℕ → ℝ

/-- An admissible sample path: arrivals are simple, start at time `≥ 0` and are locally finite
(`A n → ∞`); service and patience times are strictly positive. Under the paper's model (Poisson
arrivals, continuous service and patience laws on `[0, ∞)`) almost every path is admissible. -/
def Stream.Admissible (x : Stream) : Prop :=
  StrictMono x.A ∧ 0 ≤ x.A 0 ∧ Tendsto x.A atTop atTop ∧ (∀ n, 0 < x.S n) ∧ (∀ n, 0 < x.T n)

/-- Amount of service customer `n` has received by time `t` under the schedule `δ`
(`δ n u = 1` iff customer `n` occupies a server at time `u`). -/
noncomputable def served (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u in (x.A n)..t, δ n u

/-- Remaining processing time of customer `n` at time `t`. -/
noncomputable def remaining (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  x.S n - served x δ n t

/-- Cumulative time customer `n` has spent in the queue (present but not in service) by time `t`. -/
noncomputable def queued (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (t - x.A n) - served x δ n t

/-- Customer `n` is in the system at time `t`: she has arrived, has positive remaining work, and her
cumulative queueing time has not reached her patience time (otherwise she has abandoned). -/
def Present (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : Prop :=
  x.A n ≤ t ∧ 0 < remaining x δ n t ∧ queued x δ n t < x.T n

/-- `δ` is an SRPT schedule of the path `x` with `s` servers (§2.1, p. 5):
1. `δ n t ∈ {0, 1}`, and each `δ n` is measurable;
2. only customers present in the system are served;
3. non-idling: the number of customers in service at time `t` is `min s (number present)`;
4. shortest remaining processing time first: every customer in service has remaining work at most
   that of every present customer who is waiting (ties are broken arbitrarily).

No class structure and no threshold enters the discipline. -/
def IsSRPTSchedule (s : ℕ) (x : Stream) (δ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n t, δ n t = 0 ∨ δ n t = 1) ∧
  (∀ n, Measurable (δ n)) ∧
  (∀ n t, δ n t = 1 → Present x δ n t) ∧
  (∀ t, {n | δ n t = 1}.ncard = min s {n | Present x δ n t}.ncard) ∧
  (∀ t n m, δ n t = 1 → Present x δ m t → δ m t = 0 → remaining x δ n t ≤ remaining x δ m t)

/-- Customer `n` has finished service by time `t`. -/
def CompletedBy (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : Prop :=
  x.A n ≤ t ∧ x.S n ≤ served x δ n t

/-- Customer `n` is eventually served (`Serv`); its negation is abandonment (`Ab`). -/
def Completes (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ t, CompletedBy x δ n t

open Classical in
/-- `1{Serv}` for customer `n`, as a real number. -/
noncomputable def servedInd (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  if Completes x δ n then 1 else 0

/-- Actual waiting time `W` of customer `n`: the total length of time she is in the system but
not in service (for an abandoning customer this equals her patience time). -/
noncomputable def waitingTime (x : Stream) (δ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  (volume {t : ℝ | Present x δ n t ∧ δ n t = 0}).toReal

/-- `N_O(t)`: number of customers who have finished service in the SRPT system by time `t`. -/
noncomputable def numCompleted (x : Stream) (δ : ℕ → ℝ → ℝ) (t : ℝ) : ℕ :=
  {n | CompletedBy x δ n t}.ncard

/-- Total service requirement of the customers who have finished service by time `t`. -/
noncomputable def completedWork (x : Stream) (δ : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ᶠ n ∈ {n | CompletedBy x δ n t}, x.S n

open Classical in
/-- Auxiliary recursion for the loss system: `lossAccAux s τ x n j` records, for `j < n`, whether
customer `j` was accepted as a class 1 customer. -/
noncomputable def lossAccAux (s : ℕ) (τ : ℝ) (x : Stream) : ℕ → ℕ → Bool
  | 0 => fun _ => false
  | n + 1 => fun j =>
      if j = n then
        decide (x.S n ≤ τ ∧
          ((Finset.range n).filter
            (fun i => lossAccAux s τ x n i = true ∧ x.A n < x.A i + x.S i)).card < s)
      else lossAccAux s τ x n j

/-- The coupled two-class preemptive priority loss system `L` with `s` servers and no waiting room
(§3.1, p. 7), class 1 part: customer `n` is class 1 iff `S n ≤ τ`; a class 1 customer is accepted
iff fewer than `s` earlier accepted class 1 customers are still in service at her arrival (class 1
preempts class 2, so class 2 customers never block class 1); an accepted class 1 customer is never
preempted and leaves at `A n + S n`. -/
noncomputable def lossAccepted (s : ℕ) (τ : ℝ) (x : Stream) (n : ℕ) : Bool :=
  lossAccAux s τ x (n + 1) n

/-- `N_{L,1}(t)`: number of class 1 customers served in the loss system by time `t`. -/
noncomputable def lossNumCompleted1 (s : ℕ) (τ : ℝ) (x : Stream) (t : ℝ) : ℕ :=
  {n | lossAccepted s τ x n = true ∧ x.A n + x.S n ≤ t}.ncard

open Classical in
/-- Average of `f` over the customers `n < N` that satisfy `c` (`0` if there are none). -/
noncomputable def classAvg (N : ℕ) (c : ℕ → Prop) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ (Finset.range N).filter c, f n) / (((Finset.range N).filter c).card : ℝ)

/-- The standing assumptions of §2.1–§2.2 (pp. 5–6): `νS` (service) and `νT` (patience) are
probability laws on `[0, ∞)`, continuous with densities (`g` the service density), with means
`1/µ` and `1/θ`; the traffic intensity is `ρ > 1`; `τ` satisfies (1),
`E[S 1(S ≤ τ)] = s_λ/λ = 1/(ρµ)`. -/
structure Standing (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ) : Prop where
  probS : IsProbabilityMeasure νS
  probT : IsProbabilityMeasure νT
  g_meas : Measurable g
  g_nonneg : ∀ x, 0 ≤ g x
  density : νS = volume.withDensity (fun x => ENNReal.ofReal (g x))
  contT : νT ≪ volume
  nonnegS : νS (Set.Iio 0) = 0
  nonnegT : νT (Set.Iio 0) = 0
  intS : Integrable id νS
  intT : Integrable id νT
  mu_pos : 0 < mu
  theta_pos : 0 < theta
  meanS : ∫ x, x ∂νS = 1 / mu
  meanT : ∫ x, x ∂νT = 1 / theta
  rho_gt : 1 < rho
  threshold : ∫ x in Set.Iic tau, x ∂νS = 1 / (rho * mu)

/-- The probability model: on `(Ω, P)`, i.i.d. `Exp(1)` seeds `E n`, i.i.d. service times
`S n ∼ νS` and i.i.d. patience times `T n ∼ νT`, all mutually independent. -/
structure IsArrivalModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (νS νT : Measure ℝ)
    (E S T : ℕ → Ω → ℝ) : Prop where
  isProb : IsProbabilityMeasure P
  measE : ∀ n, Measurable (E n)
  measS : ∀ n, Measurable (S n)
  measT : ∀ n, Measurable (T n)
  lawE : ∀ n, P.map (E n) = expMeasure 1
  lawS : ∀ n, P.map (S n) = νS
  lawT : ∀ n, P.map (T n) = νT
  indep : iIndepFun (fun i : Fin 3 × ℕ => (![E, S, T] i.1) i.2) P

/-- System `s` of the sequence (§2.2): `s` servers and Poisson arrivals of rate `λ_s = ρ µ s`,
`A n = (E 0 + ⋯ + E n) / (ρ µ s)`, with the common service and patience times. -/
noncomputable def arrivalStream {Ω : Type*} (rho mu : ℝ) (s : ℕ) (E S T : ℕ → Ω → ℝ) (ω : Ω) :
    Stream :=
  ⟨fun n => (∑ k ∈ Finset.range (n + 1), E k ω) / (rho * mu * s), fun n => S n ω, fun n => T n ω⟩

/-- `v` is the almost-sure long-run average of `f` over the customers satisfying `c`:
`P`-a.s., `classAvg N c f → v` as `N → ∞`. This is how the steady-state tagged-customer
quantities of §3.2 are read. -/
def HasLongRunAvg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℕ → Ω → Prop)
    (f : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => classAvg N (fun n => c n ω) (fun n => f n ω)) atTop (𝓝 v)

end SRPTManyServer.Collapse


