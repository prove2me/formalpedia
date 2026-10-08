-- Prove2me | Definitions.Def_PalmQueueing_Ordering_Disciplines
-- name    : PalmQueueing_Ordering_Disciplines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T01:44:37.647288+00:00
-- url     : https://prove2.me/theorems/1f1dd5ae-a0fb-43bb-9e21-77b2185e7447
-- title:
--   The GI/GI/1 queue under a non-preemptive discipline using no information on the service times
-- statement:
--   §4.1.3 concerns stationary $GI/GI/1/\infty$ queues with disciplines which are
--   **non-preemptive** and which use **no information on the service times** — FIFO, LIFO
--   non-preemptive, RANDOM (p.266). Its object is Property 4.1.3: with $\psi$ the FIFO discipline and
--   $\phi$ any discipline in that class, for all convex $f$ such that the expectations exist,
--   $E^0[f(V_\psi)] \le E^0[f(V_\phi)]$ and $E^0[f(\widetilde V_\psi)] \le E^0[f(\widetilde V_\phi)]$.
--
--   This module builds the queue the interchange argument (Lemmas 4.1.3 and 4.1.4) is about.
--
--   * **Input.** $A = \sum_{k\ge0}\delta_{T_k,\sigma_k}$ on $\mathbb{R}_+\times\mathbb{R}_+$ (p.267):
--     arrival times $T_0 < T_1 < \cdots$, $T_0 \ge 0$, with i.i.d. inter-arrival times; i.i.d.
--     non-negative service times $\sigma_k$; the arrival and service sequences independent. A
--     randomised discipline (RANDOM) may also use an external random sequence $U$ independent of both.
--     This is `GIGIInput`.
--   * **Discipline.** A single server, never idle while a customer is present. At each decision epoch
--     $t$ (the server is free and a customer is present) the discipline chooses which present customer
--     to take into service, and serves him to completion (non-preemption). The choice may depend on the
--     list of customers already taken into service, on $t$, on the whole arrival sequence, on the
--     service times of the customers who already started their service, and on $U$ — the information
--     of the book's $\sigma$-field $\mathcal{G}_t$ (p.267) — but not on the service time of any
--     customer not yet started. The rule is measurable. FIFO ($\psi$) takes the earliest arrived
--     customer.
--   * **Observables.** From the resulting schedule: $B_k$ and $D_k = B_k + \sigma_k$, the times at
--     which customer $k$ begins and leaves his service; the right-continuous congestion process $I_t$,
--     the number of customers present at $t$; and $S_n$, the residual service state at $T_n$, recorded
--     as the residual service time of the customer in service together with the multiset of the service
--     times of the waiting customers.
--   * **The permutations.** $\gamma_n$ (p.268): run $\phi$ on $A_{[0,n]}$ and let $\gamma_n(m)$ be the
--     customer served $m$-th, for $m \le n$, the identity beyond $n$; $\gamma = \lim_n \gamma_n$
--     (4.1.19). The page calls $\gamma_n(k)$ "the rank with which customer $k$ leaves"; (4.1.20) and
--     $A^n = \sum_k \delta_{T_k,\sigma_{\gamma_n(k)}}$ need the inverse reading, rank to customer,
--     which is the one used.
--   * **Equivalence in law.** $A^\gamma = \sum_k \delta_{T_k,\sigma_{\gamma(k)}}$ is equivalent in
--     distribution to $A$ when $(T, \sigma\circ\gamma)$ and $(T,\sigma)$ have the same law.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §4.1.3, pp. 266-270

import Mathlib

/-!
# Service disciplines and the interchange argument (§4.1.3, pp.266-270)

§4.1.3 is "concerned with stationary `GI/GI/1/∞` queues with disciplines which are
*non-preemptive* and which use *no information on the service times*. Common examples of such
disciplines are FIFO, LIFO non-preemptive or RANDOM" (p.266). Lemmas 4.1.3 and 4.1.4 compare the
queue run under such a discipline `φ` with the FIFO queue `ψ` fed by a reordered service sequence.

This module builds that queue. A discipline is a **selection rule**: whenever the single server is
free and customers are present (a *decision epoch* `t`), it chooses which present customer to take
into service next, and that customer is then served to completion (non-preemption). The rule sees
exactly the information of the book's `σ`-field `𝒢_t` (p.267) — the whole arrival process and the
service times of the customers who already started their service — plus, for randomised rules such
as RANDOM, an external random sequence `U`. It never sees the service time of a customer that has
not started. The server is never idle while a customer is present.

Everything is a deterministic function of the input `(T, σ, U)`; the probabilistic model is the
`GIGIInput` structure at the end.
-/

namespace PalmQueueing.Ordering

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- A **non-preemptive discipline using no information on the service times** (§4.1.3, p.266).

At a decision epoch, `sel l t T s u` is the customer the discipline wants to serve next, where
* `l` is the list of customers already taken into service, in the order they were taken;
* `t` is the epoch;
* `T` is the whole arrival sequence (the arrival process is part of `𝒢_t`, p.267);
* `s` is the service-time sequence **masked** to the customers of `l` (`s k = σ_k` if `k ∈ l`,
  `0` otherwise): the service times of customers who started their service before `t`;
* `u` is an external randomisation sequence (ignored by FIFO or LIFO, used by RANDOM).

If `sel` names a customer that is not waiting, the oldest waiting customer is served instead
(`pick`), so every rule defines a valid discipline. `sel` is measurable in its continuous
arguments, as any discipline the book has in mind is. -/
structure Discipline where
  /-- The selection rule. -/
  sel : List ℕ → ℝ → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ
  /-- The rule is measurable in `(t, T, s, u)` for each history `l`. -/
  measurable_sel : ∀ l : List ℕ,
    Measurable fun p : ℝ × (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) => sel l p.1 p.2.1 p.2.2.1 p.2.2.2

/-- `ψ`, the **FIFO** discipline: serve the lowest-indexed (earliest arrived) customer not yet
taken into service. -/
noncomputable def fifo : Discipline where
  sel l _ _ _ _ := sInf {k | k ∉ l}
  measurable_sel _ := measurable_const

/-- The state of the queue after some number of decision epochs: the customers taken into service
so far, in order, and the time at which the server becomes free. -/
structure SchedState where
  /-- Customers already taken into service, in the order they were taken. -/
  served : List ℕ
  /-- The time at which the server finishes its current work. -/
  free : ℝ

/-- The customers of the input `cust` not yet taken into service. -/
def unserved (cust : Set ℕ) (s : SchedState) : Set ℕ := {k | k ∈ cust ∧ k ∉ s.served}

/-- The next decision epoch: the server is free and, since arrivals are in index order, the
earliest unserved customer has arrived (the server idles until then if the queue is empty). -/
noncomputable def epoch (cust : Set ℕ) (T : ℕ → ℝ) (s : SchedState) : ℝ :=
  max s.free (T (sInf (unserved cust s)))

/-- The customers waiting at the next decision epoch. -/
def waiting (cust : Set ℕ) (T : ℕ → ℝ) (s : SchedState) : Set ℕ :=
  {k | k ∈ unserved cust s ∧ T k ≤ epoch cust T s}

/-- The customer taken into service at the next decision epoch. -/
noncomputable def pick (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (s : SchedState) : ℕ :=
  if φ.sel s.served (epoch cust T s) T (fun k => if k ∈ s.served then σ k else 0) U
      ∈ waiting cust T s then
    φ.sel s.served (epoch cust T s) T (fun k => if k ∈ s.served then σ k else 0) U
  else sInf (unserved cust s)

/-- One decision epoch: take `pick` into service and serve it to completion (non-preemption). -/
noncomputable def step (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (s : SchedState) :
    SchedState :=
  if (unserved cust s).Nonempty then
    ⟨s.served ++ [pick φ cust T σ U s], epoch cust T s + σ (pick φ cust T σ U s)⟩
  else s

/-- The queue fed by the customers `cust` with arrival times `T` and service times `σ`, run under
`φ` from an empty system (customer `0` finds an empty queue): the state after `m` epochs. -/
noncomputable def run (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) : ℕ → SchedState
  | 0 => ⟨[], T 0⟩
  | m + 1 => step φ cust T σ U (run φ cust T σ U m)

/-- Customer `k` is the `m`-th customer taken into service (ranks start at `0`). -/
def ServedAt (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k m : ℕ) : Prop :=
  (unserved cust (run φ cust T σ U m)).Nonempty ∧ pick φ cust T σ U (run φ cust T σ U m) = k

/-- Customer `k` is eventually taken into service. -/
def IsServed (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ m, ServedAt φ cust T σ U k m

/-- `B_k`, the time at which customer `k` begins his service (`0` if he never does). -/
noncomputable def beginTime (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h : ∃ m, ServedAt φ cust T σ U k m then epoch cust T (run φ cust T σ U (Nat.find h)) else 0

/-- `D_k = B_k + σ_k`, the time at which customer `k` leaves (non-preemption). -/
noncomputable def departTime (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k : ℕ) : ℝ :=
  beginTime φ cust T σ U k + σ k

/-- `I_t`, the right-continuous congestion process: the number of customers arrived by `t` who
have not left by `t`. -/
noncomputable def congestion (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (t : ℝ) : ℕ∞ :=
  Set.encard {k | k ∈ cust ∧ T k ≤ t ∧
    ¬ (IsServed φ cust T σ U k ∧ departTime φ cust T σ U k ≤ t)}

/-- `S_n = S_{T_n}`, the residual service time vector at the `n`-th arrival (p.267), recorded as
the residual service time of the customer in service (`0` if the server is idle) together with the
multiset of the service times of the customers waiting. With strictly increasing arrival times
only customers `0, …, n` can be present at `T_n`. The book lists the coordinates of `S_n` in an
order specific to each discipline (`S_n(A, φ) = φ(β¹_n, …, σ_n)`, p.268); the discipline-free
content of that vector is this pair. -/
noncomputable def residualState (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (n : ℕ) :
    ℝ × Multiset ℝ :=
  (∑ k ∈ Finset.range (n + 1),
      if IsServed φ cust T σ U k ∧ beginTime φ cust T σ U k ≤ T n ∧
          T n < departTime φ cust T σ U k
      then departTime φ cust T σ U k - T n else 0,
    (((Finset.range (n + 1)).filter fun k => k ∈ cust ∧ T k ≤ T n ∧
        ¬ (IsServed φ cust T σ U k ∧ beginTime φ cust T σ U k ≤ T n)).val.map σ))

/-- `γ_n` of Lemma 4.1.3's proof (p.268): run `φ` on `A_{[0,n]}` (customers `0, …, n` only) and
let `γ_n(m)` be the customer served `m`-th, for `m ≤ n`; `γ_n` is the identity beyond `n`.

Direction: the page calls `γ_n(k)` "the rank with which customer `k` leaves", but (4.1.20),
`B_{γ(n)}(A, φ) = B_n(A', ψ)`, and `A^n = Σ_k δ_{T_k, σ_{γ_n(k)}}` both need `γ_n` to map a rank
to the customer of that rank; that is the reading taken here. -/
noncomputable def rankPerm (φ : Discipline) (T σ U : ℕ → ℝ) (n : ℕ) : ℕ → ℕ := fun m =>
  if m ≤ n then pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m) else m

/-- `γ = lim_n γ_n` (4.1.19, p.270): the eventual value of `γ_n(k)` (the identity where
`γ_n(k)` does not settle). -/
noncomputable def limitPerm (φ : Discipline) (T σ U : ℕ → ℝ) : ℕ → ℕ := fun k =>
  if h : ∃ N, ∀ n ≥ N, rankPerm φ T σ U n k = rankPerm φ T σ U N k then
    rankPerm φ T σ U (Nat.find h) k
  else k

/-- `γ` differs from the identity on `{0, 1, …, n}` only (Lemma 4.1.3, p.268). -/
def PermFixedBeyond (g : ℕ → ℕ) (n : ℕ) : Prop :=
  Function.Bijective g ∧ ∀ k : ℕ, n < k → g k = k

/-- The `GI/GI` input `A = Σ_{k≥0} δ_{T_k, σ_k}` on `ℝ₊ × ℝ₊` (p.267) of §4.1.3's queues, together
with the external randomisation `U` a randomised discipline may use: arrival times strictly
increasing and non-negative, i.i.d. inter-arrival times, i.i.d. non-negative service times, the
arrival sequence independent of the service sequence, and `U` independent of both. -/
structure GIGIInput (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- Arrival time of customer `k`. -/
  T : ℕ → Ω → ℝ
  /-- Service time of customer `k`. -/
  sigma : ℕ → Ω → ℝ
  /-- External randomisation available to the discipline. -/
  U : ℕ → Ω → ℝ
  measurable_T : ∀ k, Measurable (T k)
  measurable_sigma : ∀ k, Measurable (sigma k)
  measurable_U : ∀ k, Measurable (U k)
  T_zero_nonneg : ∀ ω, 0 ≤ T 0 ω
  T_strictMono : ∀ ω, StrictMono fun k => T k ω
  sigma_nonneg : ∀ k ω, 0 ≤ sigma k ω
  /-- The inter-arrival times `τ_k = T_{k+1} − T_k` are independent … -/
  indep_tau : iIndepFun (fun k ω => T (k + 1) ω - T k ω) P
  /-- … and identically distributed. -/
  ident_tau : ∀ k, IdentDistrib (fun ω => T (k + 1) ω - T k ω) (fun ω => T 1 ω - T 0 ω) P P
  /-- The service times are independent … -/
  indep_sigma : iIndepFun sigma P
  /-- … and identically distributed. -/
  ident_sigma : ∀ k, IdentDistrib (sigma k) (sigma 0) P P
  /-- Arrivals, services and the randomisation are mutually independent. -/
  indep_input : iIndepFun (fun (i : Fin 3) (ω : Ω) (k : ℕ) => ![T, sigma, U] i k ω) P

/-- The reordered input `A^γ = Σ_k δ_{T_k, σ_{γ(k)}}` is **equivalent in distribution** to `A`:
the law of `(T, σ ∘ γ)` under `P` is the law of `(T, σ)`. -/
def SameInputLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T σ : ℕ → Ω → ℝ)
    (g : Ω → ℕ → ℕ) : Prop :=
  Measure.map (fun ω => (fun k => T k ω, fun k => σ (g ω k) ω)) P
    = Measure.map (fun ω => (fun k => T k ω, fun k => σ k ω)) P

end PalmQueueing.Ordering


