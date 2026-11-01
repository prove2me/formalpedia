-- Prove2me | Definitions.Def_PerfCorrMSQ_System
-- name    : PerfCorrMSQ_System
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:25.378987+00:00
-- url     : https://prove2.me/theorems/80807e4f-969a-43f6-9fff-23f2d9dfc4ca
-- title:
--   The $n$-th system on one sample path: primitives, FIFO construction, and the processes $X^n, Q^n, Z^n_i, Q^n_0, T^n_0, w^n, M^n_i, F^n, U^n_i, V^n, L^n(0)$
-- statement:
--   The $n$-th system $M/M_{pc}/n+M_{pc}$ on one sample path, with $\mu=1$ and patience rate $\theta$. Its **primitives** are: $q_0$ customers waiting at time $0$, with elapsed waits $\ell_i$ and remaining patience times $T'_i$ ($i<q_0$, in queue order); $z_0$ customers in service at time $0$, with remaining phase-1 times $r_j$ and phase-2 times $\hat S_j$ ($j<z_0$); interarrival times $\tau_k$ with arrival epochs $E_k=\tau_0+\dots+\tau_k$, and service requirements $S_k$ of the arrivals, whose patience is $T_k=S_k/\theta$.
--
--   Customers who ever wait are indexed in FIFO order: first the $q_0$ initial waiting customers (joining at time $0$, deadline $T'_i$, service requirement $\theta(\ell_i+T'_i)$), then arrival $k$ as customer $q_0+k$ (joining at $E_k$, deadline $E_k+S_k/\theta$, service requirement $S_k$). Server $j<z_0$ is free at $r_j+\hat S_j$, the others at $0$. The FIFO recursion `PerfCorrMSQ.FifoAbandon` then gives each customer's service start or abandonment. A served customer's phase 1 lasts $\theta$ times its total waiting time (2.1), and phase 2 the rest.
--
--   From this construction (all counts at time $t$):
--
--   1. $A^n(t)$ arrivals by $t$; $Q^n(t)$ customers waiting; $Z^n(t)$ customers in service; $X^n=Q^n+Z^n$;
--   2. $Z^n_1(t)$ customers in phase 1, $Z^n_2=Z^n-Z^n_1$; $Z^n_0(t)$ initial customers in phase 1; $Q^n_0(t)$ initial waiting customers still waiting;
--   3. $T^n_0$ the time the last initial waiting customer leaves the queue ($0$ if none); $w^n(t)=\min(t,\text{wait of the head of the line})$, $0$ if the queue is empty;
--   4. $D^n(t)$ service completions and $R^n(t)$ abandonments in $(0,t]$;
--   5. $M^n_A(t)=A^n(t)-\lambda_nt$, $M^n_S(t)=D^n(t)-\int_0^tZ^n_2$, $M^n_R(t)=R^n(t)-\theta\int_0^tQ^n$;
--   6. $F^n(s,t)=\#\{k:E_k\le s,\ E_k+T_k>t\}+\theta^{-1}\lambda_n(e^{-\theta t}-e^{-\theta(t-s)})$ (4.9);
--   7. $U^n_1(t)=\int_{(T^n_0\wedge t,t]}1\{\theta w^n(s-)+s>t\}\,dM^n_S(s)$ (4.6), $U^n_2(t)=F^n(t,t)-F^n(t-w^n(t),t)$ (4.10);
--   8. $V^n(t)=\int_{T^n_0\wedge t}^t(\theta w^n(s)\wedge(t-s))Z^n_2(s)\,ds-\int_0^t\lambda_n(1-e^{-\theta w^n(s)})\,ds$ (4.13);
--   9. $L^n(0)=\sum_{j<z_0}r_j+\sum_{i<q_0}\ell_i$ (3.8).
--
--   These are the processes of every statement of the mission.
--
--   **Formalization Note** Time is real; only $t\ge0$ is used. Counts are `Set.ncard`, a junk $0$ only on the null event of infinitely many arrivals in bounded time. Stieltjes integrals against $D^n$ are sums over its jump epochs in the half-open interval; $w^n(s-)$ is `Function.leftLim`. Interval integrals are Bochner integrals of paths that are a.s. piecewise constant or piecewise linear, hence integrable on bounded intervals. Customers in phase 2 at time $0$ have $r_j=0$, so summing $r_j$ over all $j<z_0$ is the sum over those in phase 1.
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, §2 pp.4–5, §3.3 p.9 ((3.8)), §4 pp.10–12 ((4.3)–(4.13))

import Mathlib
import Definitions.Def_PerfCorrMSQ_FifoAbandon

open MeasureTheory
open scoped NNReal

namespace PerfCorrMSQ

/-!
The `n`-th system `M/M_pc/n + M_pc` of Yu–Perry (arXiv:2008.12890v1, §2 p.4–5, §3.3 p.9, §4
pp.10–12) on one sample path: primitives, the FIFO construction, and every process of the paper.

**Formalization Notes.**
* Service rate `µ = 1` (p.5, "without loss of generality"); `θ > 0` is the patience rate, and the
  patience of an arriving customer is `T = S/θ` for its service requirement `S` (perfect
  correlation, p.5).
* Time is real; only times `t ≥ 0` are used.
* **Customer indexing.** The customers who ever wait in the queue are indexed by `c : ℕ` in FIFO
  order: first the `q₀` initial waiting customers (`c < q₀`, in queue order), then the arrivals,
  arrival `k` (`k = 0, 1, …`, the paper's `k + 1`-st arrival) being customer `q₀ + k`. The `z₀`
  customers in service at time `0` are indexed separately by `j < z₀`.
* **Initial customers (§3.3, p.9).** Initial in-service customer `j` has remaining phase-1 time
  `r j` and then a phase-2 time `Sb j`. Initial waiting customer `i` has waited `ell i` before
  time `0` and has remaining patience `Tq i`; if served it needs `θ (ell i + Tq i)` time units, so
  that, as for every customer (2.1), phase 1 lasts `θ × (total wait)`.
* **Tie convention.** A customer is served iff its service could start strictly before its
  deadline (`PerfCorrMSQ.serveStep`).
* **Counts** are `Set.ncard`. A count is a junk `0` only if the set is infinite, which happens only
  on the null event that infinitely many arrivals occur in a bounded time interval.
* **Integrals** `∫_a^b … ds` are interval integrals of piecewise-constant paths; Stieltjes
  integrals `∫_a^b … dDⁿ(s)` against a counting process are sums over its jump epochs in
  `(a, b]`. Left limits `wⁿ(s−)` are `Function.leftLim`.
-/

/-- The **primitives of one system on one sample path**: `q0` customers waiting at time `0`
with elapsed waits `ell i` (`i < q0`) and remaining patience times `Tq i`; `z0` customers in
service at time `0` with remaining phase-1 times `r j` and phase-2 times `Sb j` (`j < z0`); the
interarrival times `tau k` and the service requirements `S k` of the arrivals after time `0`
(`k : ℕ`). Entries beyond `q0`, `z0` are never used. -/
structure Prim where
  q0 : ℕ
  z0 : ℕ
  ell : ℕ → ℝ
  r : ℕ → ℝ
  tau : ℕ → ℝ
  S : ℕ → ℝ
  Tq : ℕ → ℝ
  Sb : ℕ → ℝ

namespace Prim

variable (θ : ℝ) (n : ℕ) (p : Prim)

/-- The arrival epoch `Eₖ = τ₀ + ⋯ + τₖ` of arrival `k` (the paper's `Eⁿ_{k+1}`, p.10). -/
def arrEpoch (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), p.tau i

/-- The time customer `c` joins the queue: `0` for an initial waiting customer, its arrival
epoch for an arrival. -/
noncomputable def arr (c : ℕ) : ℝ := if c < p.q0 then 0 else p.arrEpoch (c - p.q0)

/-- The remaining patience of customer `c` from the time it joins the queue: `Tq c` for an
initial waiting customer, `S/θ` for an arrival (perfect correlation `T = S/θ`, p.5). -/
noncomputable def patience (c : ℕ) : ℝ := if c < p.q0 then p.Tq c else p.S (c - p.q0) / θ

/-- The abandonment deadline of customer `c`. -/
noncomputable def deadline (c : ℕ) : ℝ := p.arr c + p.patience θ c

/-- The wait customer `c` accumulated before time `0` (`ell c` for an initial waiting customer,
`0` for an arrival). -/
noncomputable def preWait (c : ℕ) : ℝ := if c < p.q0 then p.ell c else 0

/-- The service requirement of customer `c`: `S` for an arrival, `θ (ell + Tq)` for an initial
waiting customer (phase 1 `θ × total wait`, then phase 2, (2.1)). -/
noncomputable def req (c : ℕ) : ℝ := if c < p.q0 then θ * (p.ell c + p.Tq c) else p.S (c - p.q0)

/-- The free time of initial server `j < n`: `r j + Sb j` if it serves an initial customer
(`j < z0`), `0` if it is idle at time `0`. -/
noncomputable def initFreeTime (j : ℕ) : ℝ := if j < p.z0 then p.r j + p.Sb j else 0

/-- The sorted list of the `n` server free times at time `0`. -/
noncomputable def initFree : List ℝ :=
  ((List.range n).map p.initFreeTime).insertionSort (· ≤ ·)

/-- Service-start time of customer `c` in the FIFO recursion (`none` if it abandons). -/
noncomputable def start (c : ℕ) : Option ℝ :=
  startTime (p.initFree n) p.arr (p.deadline θ) (p.req θ) c

/-- The time customer `c` leaves the queue (enters service or abandons). -/
noncomputable def exitQ (c : ℕ) : ℝ := (p.start θ n c).getD (p.deadline θ c)

/-- The time customer `c` leaves the system. -/
noncomputable def dep (c : ℕ) : ℝ :=
  match p.start θ n c with
  | some s => s + p.req θ c
  | none => p.deadline θ c

/-- Customer `c` is waiting in the queue at time `t`. -/
def Waiting (t : ℝ) (c : ℕ) : Prop := p.arr c ≤ t ∧ t < p.exitQ θ n c

/-- Customer `c` is in service at time `t`. -/
def InService (t : ℝ) (c : ℕ) : Prop :=
  ∃ s, p.start θ n c = some s ∧ s ≤ t ∧ t < s + p.req θ c

/-- Customer `c` is in phase-1 service at time `t`: it started at `s ≤ t` and phase 1 lasts
`θ × (total wait) = θ (preWait c + s − arr c)` ((2.1), p.5). -/
def InPhase1 (t : ℝ) (c : ℕ) : Prop :=
  ∃ s, p.start θ n c = some s ∧ s ≤ t ∧ t < s + θ * (p.preWait c + (s - p.arr c))

/-- `Aⁿ(t)`: the number of arrivals by time `t`. -/
noncomputable def A (t : ℝ) : ℕ := {k : ℕ | p.arrEpoch k ≤ t}.ncard

/-- `Qⁿ(t)`: the number of customers waiting in queue at time `t`. -/
noncomputable def Q (t : ℝ) : ℕ := {c : ℕ | p.Waiting θ n t c}.ncard

/-- `Zⁿ(t)`: the number of customers in service at time `t`. -/
noncomputable def Z (t : ℝ) : ℕ :=
  {j : ℕ | j < p.z0 ∧ t < p.r j + p.Sb j}.ncard + {c : ℕ | p.InService θ n t c}.ncard

/-- `Xⁿ(t) = Zⁿ(t) + Qⁿ(t)`: the number of customers in the system at time `t`. -/
noncomputable def X (t : ℝ) : ℕ := p.Q θ n t + p.Z θ n t

/-- `Zⁿ₁(t)`: the number of customers in phase-1 service at time `t`. -/
noncomputable def Z1 (t : ℝ) : ℕ :=
  {j : ℕ | j < p.z0 ∧ t < p.r j}.ncard + {c : ℕ | p.InPhase1 θ n t c}.ncard

/-- `Zⁿ₂(t) = Zⁿ(t) − Zⁿ₁(t)`: the number in phase-2 service. -/
noncomputable def Z2 (t : ℝ) : ℝ := (p.Z θ n t : ℝ) - p.Z1 θ n t

/-- `Zⁿ₀(t)`: the number of initial customers (in service or waiting at time `0`) who are in
phase-1 service at time `t` (p.10). -/
noncomputable def Z0 (t : ℝ) : ℕ :=
  {j : ℕ | j < p.z0 ∧ t < p.r j}.ncard + {c : ℕ | c < p.q0 ∧ p.InPhase1 θ n t c}.ncard

/-- `Qⁿ₀(t)`: the number of initial waiting customers still waiting at time `t` (p.11). -/
noncomputable def Q0 (t : ℝ) : ℕ := {c : ℕ | c < p.q0 ∧ p.Waiting θ n t c}.ncard

/-- `Tⁿ₀`: the time at which the last initial waiting customer leaves the queue, `0` if there is
none (p.10). -/
noncomputable def T0 : ℝ :=
  (((Finset.range p.q0).sup fun c => Real.toNNReal (p.exitQ θ n c)) : ℝ≥0)

open Classical in
/-- `wⁿ(t)`: the minimum of `t` and the waiting time of the head-of-line customer (the least
index waiting, by FIFO), whose waiting time is `preWait + t − arr`; `0` if nobody waits (p.10). -/
noncomputable def w (t : ℝ) : ℝ :=
  if {c : ℕ | p.Waiting θ n t c}.Nonempty then
    min t (p.preWait (sInf {c : ℕ | p.Waiting θ n t c}) + t -
      p.arr (sInf {c : ℕ | p.Waiting θ n t c}))
  else 0

/-- The number of service completions at epochs `e > 0` satisfying `P e`: initial in-service
customers complete at `r j + Sb j`, served queue customers at `start + req`. With `P e := e ≤ t`
this is `Dⁿ(t)`; for a predicate `P` it is the Stieltjes integral `∫ 1{P} dDⁿ` over `(0, ∞)`. -/
noncomputable def complCount (P : ℝ → Prop) : ℕ :=
  {j : ℕ | j < p.z0 ∧ 0 < p.r j + p.Sb j ∧ P (p.r j + p.Sb j)}.ncard +
    {c : ℕ | ∃ s, p.start θ n c = some s ∧ 0 < s + p.req θ c ∧ P (s + p.req θ c)}.ncard

/-- `Dⁿ(t)`: the number of service completions in `(0, t]`. -/
noncomputable def D (t : ℝ) : ℕ := p.complCount θ n (· ≤ t)

/-- `Rⁿ(t)`: the number of abandonments in `(0, t]`. -/
noncomputable def R (t : ℝ) : ℕ :=
  {c : ℕ | p.start θ n c = none ∧ 0 < p.deadline θ c ∧ p.deadline θ c ≤ t}.ncard

/-- `Mⁿ_A(t) = Aⁿ(t) − λₙ t` (p.11). -/
noncomputable def MA (lam t : ℝ) : ℝ := (p.A t : ℝ) - lam * t

/-- `Mⁿ_S(t) = Dⁿ(t) − ∫₀ᵗ Zⁿ₂(s) ds` (p.11). -/
noncomputable def MS (t : ℝ) : ℝ := (p.D θ n t : ℝ) - ∫ s in (0 : ℝ)..t, p.Z2 θ n s

/-- `Mⁿ_R(t) = Rⁿ(t) − θ ∫₀ᵗ Qⁿ(s) ds` (p.11). -/
noncomputable def MR (t : ℝ) : ℝ := (p.R θ n t : ℝ) - θ * ∫ s in (0 : ℝ)..t, (p.Q θ n s : ℝ)

/-- `Fⁿ(s, t)` (4.9): the number of arrivals in `(0, s]` whose patience outlasts `t`,
`∫₀ˢ 1{E_{A(u)} + T_{A(u)} > t} dAⁿ(u)`, plus `θ⁻¹λₙ(e^{−θt} − e^{−θ(t−s)})`. -/
noncomputable def F (lam s t : ℝ) : ℝ :=
  ({k : ℕ | p.arrEpoch k ≤ s ∧ t < p.arrEpoch k + p.S k / θ}.ncard : ℝ) +
    θ⁻¹ * lam * (Real.exp (-(θ * t)) - Real.exp (-(θ * (t - s))))

/-- `Uⁿ₁(t)` (4.6): `∫_{(Tⁿ₀ ∧ t, t]} 1{θ wⁿ(s−) + s > t} dMⁿ_S(s)`, i.e. the number of service
completions at epochs `s ∈ (Tⁿ₀ ∧ t, t]` with `θ wⁿ(s−) + s > t`, minus
`∫_{Tⁿ₀ ∧ t}^t 1{θ wⁿ(s−) + s > t} Zⁿ₂(s) ds`. -/
noncomputable def U1 (t : ℝ) : ℝ :=
  (p.complCount θ n (fun e => min (p.T0 θ n) t < e ∧ e ≤ t ∧
      t < θ * Function.leftLim (p.w θ n) e + e) : ℝ) -
    ∫ s in (min (p.T0 θ n) t)..t,
      (if t < θ * Function.leftLim (p.w θ n) s + s then (1 : ℝ) else 0) * p.Z2 θ n s

/-- `Uⁿ₂(t) = Fⁿ(t, t) − Fⁿ(t − wⁿ(t), t)` (4.10). -/
noncomputable def U2 (lam t : ℝ) : ℝ := p.F θ lam t t - p.F θ lam (t - p.w θ n t) t

/-- `Vⁿ(t)` (4.13): `∫_{Tⁿ₀ ∧ t}^t (θ wⁿ(s)) ∧ (t − s) Zⁿ₂(s) ds − ∫₀ᵗ λₙ(1 − e^{−θ wⁿ(s)}) ds`. -/
noncomputable def V (lam t : ℝ) : ℝ :=
  (∫ s in (min (p.T0 θ n) t)..t, min (θ * p.w θ n s) (t - s) * p.Z2 θ n s) -
    ∫ s in (0 : ℝ)..t, lam * (1 - Real.exp (-(θ * p.w θ n s)))

/-- `Lⁿ(0)` ((3.8) at `t = 0`): the total remaining phase-1 time of the initial customers in
service plus the total elapsed wait of the initial customers in queue. (Customers in phase 2 have
remaining phase-1 time `0`, so summing over all `j < z0` is the sum over those in phase 1.)

**Formalization Note.** (3.8) calls `rⁿⱼ(t)` the "remaining service time" of a customer in phase 1;
it is read as the remaining phase-1 time, as in the equality for `Zⁿ₀ + Zⁿ₁` on p.11 and the bound
`gⁿᵢ(t) ≤ rⁿᵢ(0)` on p.20. This is the smaller quantity, so (Ia), (Ib) are the weaker hypotheses. -/
noncomputable def L0 : ℝ :=
  (∑ j ∈ Finset.range p.z0, p.r j) + ∑ i ∈ Finset.range p.q0, p.ell i

end Prim

end PerfCorrMSQ


