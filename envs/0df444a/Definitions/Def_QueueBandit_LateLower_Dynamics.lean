-- Prove2me | Definitions.Def_QueueBandit_LateLower_Dynamics
-- name    : QueueBandit_LateLower_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:59.433321+00:00
-- url     : https://prove2.me/theorems/385dea14-d8e5-49c5-9e47-13401dac54ef
-- title:
--   §3.2, pp. 6–8, Definition 2 p. 12 — switch dynamics, scheduling policies, genie Q*, queue-regret Ψ_u(t), counts T_uk(t+1), α-consistency
-- statement:
--   Fix an instance $(\lambda,\mu)$ of a switch with $U$ queues and $K\ge U$ servers. Time is slotted, $t=1,2,\dots$. In slot $t$ each queue $u$ receives an arrival $A_u(t)\sim\mathrm{Bernoulli}(\lambda_u)$ and every link $(u,k)$ offers a service $R_{uk}(t)\sim\mathrm{Bernoulli}(\mu_{uk})$; all of these are independent and i.i.d. over slots. They are realised from independent uniform seeds $W_u(t),V_{uk}(t)$ on $[0,1]$ as
--   $$A_u(t)=\mathbf 1\{W_u(t)\le\lambda_u\},\qquad R_{uk}(t)=\mathbf 1\{V_{uk}(t)\le\mu_{uk}\}.$$
--
--   In each slot the scheduler chooses a **matching** $\kappa(t)$: queue $u$ is assigned server $\kappa_u(t)$, and distinct queues get distinct servers. A **scheduling policy** chooses $\kappa(t)$ as a function of the past schedules $\kappa(1),\dots,\kappa(t-1)$, the services $S(1),\dots,S(t-1)$ observed on the scheduled links, and a private uniform seed of slot $t$; arrivals and queue lengths are not observed. Every randomized history-dependent policy is of this form.
--
--   The service received by queue $u$ is $S_u(t)=R_{u\kappa_u(t)}(t)$, and the queue lengths evolve as
--   $$Q_u(t)=\big(Q_u(t-1)+A_u(t)-S_u(t)\big)^+ .$$
--   The **genie** always schedules the optimal matching $k^*$; on the same initial state $Q^*(0)=Q(0)$ and the same arrivals and offered services, $S^*_u(t)=R_{uk^*_u}(t)$ and $Q^*_u(t)=(Q^*_u(t-1)+A_u(t)-S^*_u(t))^+$. The initial state $Q(0)$ has an arbitrary law $\nu$ on $\mathbb N^U$ and is independent of all seeds. The **queue-regret** of queue $u$ is
--   $$\Psi_u(t)=\mathbb E\big[Q_u(t)-Q^*_u(t)\big].$$
--
--   The number of the first $t$ slots in which queue $u$ is served by server $k$ is $T_{uk}(t+1)=\sum_{s=1}^t\mathbf 1\{\kappa_u(s)=k\}$.
--
--   **Definition 2 ($\alpha$-consistency).** For $\alpha\in(0,1)$, a policy is $\alpha$-consistent if for every problem instance with a unique optimal matching there is a constant $C$, which may depend on the instance, such that
--   $$\mathbb E\Big[\sum_{s=1}^t\mathbf 1\{\kappa_u(s)=k\}\Big]\le C\,t^\alpha\qquad\text{for all } t\ge1,\ u\in[U],\ k\neq k^*_u .$$
--
--   **Formalization Note** The probability space is canonical: $\Omega=\mathbb N^U\times(\text{Seed})^{\mathbb N}$ with law $\nu\otimes\mathrm{Unif}^{\otimes\mathbb N}$, where a seed holds one uniform per arrival, one per link and one for the scheduler; slot $t\ge1$ uses seed $t$. A policy is `act n h x`: the matching of slot $n+1$ given the history $h$ of the first $n$ slots and the private seed $x$, required only to select each matching on a measurable set of seeds. The truncated subtraction on $\mathbb N$ in the queue recursion is exactly $(\cdot)^+$. The schedule depends on the seeds and on $\mu$ only, so $\mathbb E[T_{uk}(t+1)]$ is computed under the seed law and depends on neither $\lambda$ nor $\nu$; correspondingly the instances quantified over in $\alpha$-consistency are the matrices $\mu\in[0,1]^{U\times K}$ with Assumption 1. "For all $t$" in Definition 2 is read as all $t\ge1$, which is equivalent to "for all large $t$" after enlarging $C$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 6, §3.1 (dynamics and information); p. 7, §3.2; p. 8 (Ψ); p. 12, Definition 2; p. 38 (T_uk(t+1))

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance

namespace QueueBandit.LateLower

open MeasureTheory Finset
open scoped unitInterval

variable {U K : ℕ}

/-- A matching of the complete bipartite graph between the `U` queues and the `K` servers:
queue `u` is served by server `κ u`, and distinct queues get distinct servers (p. 7, p. 14). -/
abbrev Matching (U K : ℕ) := Fin U ↪ Fin K

/-- The randomness of one time slot: a uniform seed on `[0, 1]` for the arrival to each queue,
one for the service offered by each link `(u, k)`, and the scheduler's private seed. -/
abbrev Seed (U K : ℕ) := (Fin U → I) × (Fin U → Fin K → I) × I

/-- The law of one slot's seed: all coordinates independent and uniform on `[0, 1]`. -/
noncomputable def seedLaw (U K : ℕ) : Measure (Seed U K) := volume

instance (U K : ℕ) : IsProbabilityMeasure (seedLaw U K) := by
  unfold seedLaw; infer_instance

/-- The law of the whole seed sequence `(ω t)_{t ∈ ℕ}`: i.i.d. with law `seedLaw`.
Slot `t ≥ 1` uses `ω t`; `ω 0` is unused. -/
noncomputable def seedMeasure (U K : ℕ) : Measure (ℕ → Seed U K) :=
  Measure.infinitePi (fun _ : ℕ => seedLaw U K)

instance (U K : ℕ) : IsProbabilityMeasure (seedMeasure U K) := by
  unfold seedMeasure; infer_instance

/-- Arrival `A_u(t) = 1{W_u(t) ≤ λ_u}`, a Bernoulli(`λ_u`) variable. -/
noncomputable def arrival (lam : Fin U → ℝ) (ω : ℕ → Seed U K) (t : ℕ) (u : Fin U) : ℕ :=
  if (((ω t).1 u : ℝ) ≤ lam u) then 1 else 0

/-- Service offered by link `(u, k)` in slot `t`: `R_uk(t) = 1{V_uk(t) ≤ μ_uk}`, a
Bernoulli(`μ_uk`) variable. -/
noncomputable def offered (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (t : ℕ) (u : Fin U)
    (k : Fin K) : ℕ :=
  if (((ω t).2.1 u k : ℝ) ≤ mu u k) then 1 else 0

/-- What the scheduler observes about one completed slot: the matching it scheduled and the
service offered by each scheduled link. -/
abbrev Obs (U K : ℕ) := Matching U K × (Fin U → Bool)

/-- The history after `n` completed slots (slots `1, …, n`, entry `i` recording slot `i + 1`). -/
abbrev History (U K : ℕ) (n : ℕ) := Fin n → Obs U K

/-- A randomized, history-dependent scheduling policy (p. 6): after `n` completed slots it
schedules, in slot `n + 1`, the matching `act n h x`, where `h` is the history of past schedules
and observed services and `x` is a fresh private uniform seed. Arrivals and queue lengths are not
observed. The only requirement is that each matching is chosen on a measurable set of seeds. -/
structure Policy (U K : ℕ) where
  act : (n : ℕ) → History U K n → I → Matching U K
  measurableSet_act : ∀ n h m, MeasurableSet {x : I | act n h x = m}

/-- The history generated by policy `π` under service rates `mu` on the seed sequence `ω`. -/
noncomputable def hist (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) :
    (n : ℕ) → History U K n
  | 0 => Fin.elim0
  | n + 1 =>
    let κ := π.act n (hist π mu ω n) (ω (n + 1)).2.2
    Fin.snoc (α := fun _ => Obs U K) (hist π mu ω n)
      (κ, fun u => decide (offered mu ω (n + 1) u (κ u) = 1))

/-- The matching `κ(t)` scheduled in slot `t ≥ 1` (the value at `t = 0` is not used). -/
noncomputable def sched (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (t : ℕ) :
    Matching U K :=
  π.act (t - 1) (hist π mu ω (t - 1)) (ω t).2.2

/-- Service `S_u(t) = R_{u κ_u(t)}(t)` offered to queue `u` by its scheduled server. -/
noncomputable def service (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (t : ℕ)
    (u : Fin U) : ℕ :=
  offered mu ω t u (sched π mu ω t u)

/-- Service `S*_u(t) = R_{u k*_u}(t)` under the genie that always schedules the optimal matching. -/
noncomputable def genieService (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (ω : ℕ → Seed U K) (t : ℕ) (u : Fin U) : ℕ :=
  offered mu ω t u (kstar u)

/-- Queue lengths under `π`: `Q(0) = q0` and `Q_u(t) = (Q_u(t−1) + A_u(t) − S_u(t))⁺`
(truncated subtraction on `ℕ` is exactly the positive part here). -/
noncomputable def queue (π : Policy U K) (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ)
    (q0 : Fin U → ℕ) (ω : ℕ → Seed U K) : ℕ → Fin U → ℕ
  | 0 => q0
  | t + 1 => fun u => queue π lam mu q0 ω t u + arrival lam ω (t + 1) u - service π mu ω (t + 1) u

/-- Queue lengths `Q*` under the genie, driven by the same initial state, arrivals and offered
services: `Q*(0) = Q(0)` and `Q*_u(t) = (Q*_u(t−1) + A_u(t) − S*_u(t))⁺`. -/
noncomputable def genieQueue (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (q0 : Fin U → ℕ) (ω : ℕ → Seed U K) : ℕ → Fin U → ℕ
  | 0 => q0
  | t + 1 => fun u =>
    genieQueue lam mu kstar q0 ω t u + arrival lam ω (t + 1) u - genieService mu kstar ω (t + 1) u

/-- The probability law of the whole system: the initial queue-length vector `Q(0) ∼ ν`,
independent of the i.i.d. seed sequence. -/
noncomputable def sysMeasure (ν : Measure (Fin U → ℕ)) : Measure ((Fin U → ℕ) × (ℕ → Seed U K)) :=
  ν.prod (seedMeasure U K)

/-- Queue-regret `Ψ_u(t) = E[Q_u(t) − Q*_u(t)]` (p. 8). -/
noncomputable def queueRegret (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (ν : Measure (Fin U → ℕ)) (π : Policy U K) (u : Fin U) (t : ℕ) : ℝ :=
  ∫ x, ((queue π lam mu x.1 x.2 t u : ℝ) - (genieQueue lam mu kstar x.1 x.2 t u : ℝ))
    ∂(sysMeasure (K := K) ν)

/-- `T_uk(t + 1) = Σ_{s=1}^t 1{κ_u(s) = k}`, the number of the first `t` slots in which queue `u`
is served by server `k`. -/
noncomputable def count (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (u : Fin U)
    (k : Fin K) (t : ℕ) : ℕ :=
  ((Icc 1 t).filter fun s => sched π mu ω s u = k).card

/-- `E[T_uk(t + 1)]` under service rates `mu`. The schedule depends on the seeds only (not on the
arrival rates or on `Q(0)`), so the expectation is taken under the seed law. -/
noncomputable def expCount (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K)
    (t : ℕ) : ℝ :=
  ∫ ω, (count π mu ω u k t : ℝ) ∂(seedMeasure U K)

/-- Definition 2 (p. 12): `π` is `α`-consistent if for every problem instance with a unique
optimal matching (service rates in `[0, 1]`, Assumption 1) there is a constant `C`, depending on
the instance, with `E[Σ_{s=1}^t 1{κ_u(s) = k}] ≤ C t^α` for all `t ≥ 1`, all `u` and all
`k ≠ k*_u`. -/
def IsAlphaConsistent (π : Policy U K) (α : ℝ) : Prop :=
  ∀ (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K),
    (∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) → Assumption1 mu kstar →
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → ∀ u k, k ≠ kstar u → expCount π mu u k t ≤ C * (t : ℝ) ^ α

end QueueBandit.LateLower


