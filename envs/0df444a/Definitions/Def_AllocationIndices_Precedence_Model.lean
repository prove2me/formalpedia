-- Prove2me | Definitions.Def_AllocationIndices_Precedence_Model
-- name    : AllocationIndices_Precedence_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:37.66071+00:00
-- url     : https://prove2.me/theorems/49d95100-4a8b-4c4b-92a5-cd734855962c
-- title:
--   Non-preemptive ordinary jobs under precedence constraints, the family index (4.15), and FI, FI* and ε-FI* policies (§3.2, §4.6, §4.10)
-- statement:
--   The objects of §3.2, §4.6 and §4.10 for a family $\mathscr F$ of alternative bandit processes all of which are **ordinary jobs**, in the continuous-time units of the book: a reward accruing at time $t$ is discounted by $e^{-\gamma t}$, $\gamma > 0$.
--
--   1. **Jobs and precedence constraints** (§3.2, pp. 56–57; §4.6). There are $n$ jobs on a single machine. Job $i$ has a reward $V_i > 0$, received at its completion time $C_i$ and discounted to $V_i e^{-\gamma C_i}$, and no other reward. Its service time $\sigma_i$ (the process time required for its completion) has a given law with $P(\sigma_i > 0) = 1$, and $\sigma_1, \dots, \sigma_n$ are independent. A relation $i \prec j$ ("job $i$ must be completed before job $j$ may be started") gives the precedence constraints; its graph has no circuit. There are no arrivals.
--
--   2. **Non-preemptive policies.** Service is switched from one job to another only when the first job has been completed. Starting from a set $A$ of already completed jobs, a policy $g$ chooses, each time the machine becomes free, the next job to serve as a (measurable) function of the history: the jobs completed so far, in order, with their observed service times. It is **feasible** if, for every realization of the service times, each job it starts is uncompleted and all its predecessors are completed. Its payoff is
--   $$R_g(\mathscr F) = E\sum_{i \notin A} V_i e^{-\gamma C_i},$$
--   and $g$ is **optimal** if it is feasible and $R_g(\mathscr F) \ge R_{g'}(\mathscr F)$ for every feasible policy $g'$.
--
--   3. **Stages and the index (4.15)** (p. 97). A stage $(g, \tau)$ is a policy $g$ together with a positive stopping time $\tau$: after each completion, as a function of the history since the stage began, it decides whether the stage ends; at least one job is served, and the stage ends at the latest when all jobs are completed. With $T$ the time at which the stage ends,
--   $$R_{g\tau}(\mathscr F) = E\sum_{i \text{ completed in the stage}} V_i e^{-\gamma C_i}, \qquad W_{g\tau}(\mathscr F) = E\int_0^{T} e^{-\gamma t}\,dt = \gamma^{-1}E\big(1 - e^{-\gamma T}\big),$$
--   and the index of the family (with completed set $B$) is
--   $$\nu(\mathscr F) = \sup_{g, \tau} \frac{R_{g\tau}(\mathscr F)}{W_{g\tau}(\mathscr F)},$$
--   the supremum over all feasible stages. A stage $(\pi, \sigma)$ attaining the supremum is the **first stage of a modified forwards induction (FI\*) policy**. A stage is **static** if its choices and its decision to end depend only on the number of jobs completed in it: it serves a fixed set of jobs in a fixed order.
--
--   4. **Postponed first-stage rewards** (Eq. (4.16), p. 97). For a stage $(\pi, \sigma)$ from $B$ and a feasible policy $g$ from $B$, $R_{g\pi\sigma}(\mathscr F)$ and $W_{g\pi\sigma}(\mathscr F)$ are the expected discounted rewards and the expected discounted time accruing under $g$ to the jobs that would have been completed during the stage $(\pi, \sigma)$, had it been employed (with the same service times): job $i$ contributes $V_i e^{-\gamma C_i}$ and $\int_{S_i}^{C_i} e^{-\gamma t}\,dt$, where $S_i, C_i$ are its start and completion times under $g$.
--
--   5. **Policy classes** (§2.6.6, p. 33; §4.6; §4.10, p. 112). A feasible policy from $A$ is
--      - a **modified forwards induction (FI\*) policy** if it repeatedly begins an FI\* first stage of the current family (completed set: $A$ together with the jobs completed so far) and follows it until it ends;
--      - a **forwards induction (FI) policy** if at every decision time the job it starts is the first job of some FI\* first stage of the current family;
--      - an **ε-FI\* policy** if it is like an FI\* policy except that each stage is only required to have ratio $R_{g\tau}/W_{g\tau} \ge \nu(\mathscr F) - \varepsilon$, $\nu(\mathscr F)$ the index of the family when the stage begins.
--
--      Each of these three properties is required to hold with probability one over the service times.
--
--   **Formalization Note** Jobs are `Fin n`; the service-time law of job $i$ is a `ProbabilityMeasure ℝ` with no mass on $(-\infty, 0]$, and the realizations $\omega = (\sigma_1, \dots, \sigma_n)$ have the product law `serviceLaw`. A policy is deterministic: `next : List (Fin n × ℝ) → Fin n` maps the history (completed jobs with their service times) to the next job, measurably in the service times for each history length; completed jobs and idle time are never chosen, as in the book's FABP. A stage's stopping rule `stop` is checked after each completion; the stage never ends before its first completion. The index $\nu$ is a real `sSup`; for $B$ with an uncompleted job the set of stage ratios is nonempty and bounded above (by $\max_i V_i E e^{-\gamma\sigma_i}/(\gamma^{-1}(1 - E e^{-\gamma\sigma_i}))$). An FI\* policy is encoded through a rule `ρ` choosing, after every history, an FI\* first stage of the current family, and the policy must agree almost surely with the policy that runs `ρ`'s stages one after another; FI and FI\* policies and optimal policies are compared up to service-time realizations of probability zero. "Index policies" are not defined by the book for a family that is not simple; Theorem 4.9's class of index policies is read as the class of modified forwards induction policies built from the index (4.15) (the book: "a modified index policy is actually a modified forwards induction policy", p. 33).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §3.2 pp. 56–57 (jobs, non-preemption), §2.6.6 p. 33 (FI and FI* policies), §4.6 pp. 97–98 (Eqs. (4.15), (4.16)), §4.10 p. 112 (ε-FI* policies)

import Mathlib

open MeasureTheory

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
§3.2 (pp. 56–57), §4.6 (pp. 97–100) and §4.10 (p. 112): a family of alternative bandit processes
(FABP) in which every bandit process is an **ordinary job** (a single positive reward on
completion), with precedence constraints, no arrivals, and no preemption, in the continuous-time
units of the book (rewards at time `t` are discounted by `e^{−γ t}`).

* `JobFamily n` — `n` jobs on a single machine. Job `i` has reward `V_i > 0` on completion and a
  service time `σ_i > 0` with law `service i`; the `σ_i` are independent. `prec i j` means that
  job `i` must be completed before job `j` may be started; the precedence graph has no circuit.
* `History`, `Policy`, `Policy.Feasible`, `Policy.payoff`, `IsOptimalPolicy` — a non-preemptive
  policy chooses, each time the machine becomes free, the next job as a function of the jobs
  completed so far and their observed service times; from the initial set `A` of completed jobs
  it must always choose an uncompleted job all of whose predecessors are completed. Its payoff is
  `E ∑_i V_i e^{−γ C_i}` over the jobs not in `A` (`C_i` the completion time of job `i`).
* `Stage`, `Stage.reward`, `Stage.time`, `Stage.ratio`, `familyIndex` — a policy `g` together with
  a positive stopping time `τ` (a stopping rule checked after every completion), `R_{gτ}(𝓕)`,
  `W_{gτ}(𝓕) = γ⁻¹ E(1 − e^{−γ T_τ})` and the index (4.15)
  `ν(𝓕) = sup_{g, τ} R_{gτ}(𝓕) / W_{gτ}(𝓕)`.
* `IsFIStarStage` — the first stage `(π, σ)` of a modified forwards induction (FI*) policy:
  a stage attaining the supremum in (4.15).
* `postponedReward`, `postponedTime` — `R_{gπσ}(𝓕)`, `W_{gπσ}(𝓕)` of (4.16): the expected
  discounted rewards and discounted time accruing under a policy `g` to the jobs that would have
  been completed during the first stage `(π, σ)`, had that stage been employed.
* `IsFIStarPolicy`, `IsFIPolicy`, `IsEpsFIStarPolicy` — modified forwards induction (FI*)
  policies (repeat FI* stages), forwards induction (FI) policies (at every decision time start
  an FI* stage of the current family), and ε-FI* policies (stages whose ratio is within `ε` of
  `ν`), each up to a set of service-time realizations of probability zero.
-/

namespace AllocationIndices.Precedence

/-- A family of `n` ordinary jobs with precedence constraints on a single machine (§3.2, §4.6).
Job `i` yields the reward `reward i * e^{−γ t}` if it is completed at time `t`, and no other
reward; its service time has law `service i`, is positive almost surely, and the service times of
different jobs are independent (`serviceLaw`). `prec i j`: job `i` must be completed before job `j`
may be started. The precedence graph has no circuit. -/
structure JobFamily (n : ℕ) where
  /-- `V_i`, the reward on completion of job `i`. -/
  reward : Fin n → ℝ
  /-- The law of the service time `σ_i` of job `i`. -/
  service : Fin n → ProbabilityMeasure ℝ
  /-- `prec i j`: job `i` must be completed before job `j` may be started. -/
  prec : Fin n → Fin n → Prop
  /-- The discount parameter `γ`: a reward at time `t` is discounted by `e^{−γ t}`. -/
  γ : ℝ
  reward_pos : ∀ i, 0 < reward i
  service_pos : ∀ i, (service i : Measure ℝ) (Set.Iic 0) = 0
  prec_acyclic : ∀ i, ¬ Relation.TransGen prec i i
  γ_pos : 0 < γ

variable {n : ℕ}

/-- The joint law of the service times `(σ_1, …, σ_n)`: independent, `σ_i ∼ service i`. A
realization is `ω : Fin n → ℝ`, `ω i = σ_i`. -/
noncomputable def serviceLaw (F : JobFamily n) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => (F.service i : Measure ℝ)

/-- A history: the jobs completed so far (after time zero), in order of completion, each with its
observed service time. -/
abbrev History (n : ℕ) := List (Fin n × ℝ)

/-- The set of jobs completed in a history. -/
def History.jobs (h : History n) : Finset (Fin n) := (h.map Prod.fst).toFinset

/-- The time elapsed in a history: the total service time of its jobs. -/
def History.elapsed (h : History n) : ℝ := (h.map Prod.snd).sum

/-- A non-preemptive policy: each time the machine becomes free it starts the job
`next h`, a (measurable) function of the history `h` observed so far. A job, once started, is
served until it is completed. -/
structure Policy (n : ℕ) where
  /-- The job started after history `h`. -/
  next : History n → Fin n
  measurable_next : ∀ k : ℕ, Measurable fun h : Fin k → Fin n × ℝ => next (List.ofFn h)

/-- The history after `k` completions when the service times are `ω`. -/
def Policy.hist (π : Policy n) (ω : Fin n → ℝ) : ℕ → History n
  | 0 => []
  | k + 1 => π.hist ω k ++ [(π.next (π.hist ω k), ω (π.next (π.hist ω k)))]

/-- The `(k+1)`th job served (`k = 0, 1, …`). -/
def Policy.job (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) : Fin n := π.next (π.hist ω k)

/-- The time at which the `(k+1)`th job served is started. -/
def Policy.startTime (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) : ℝ := (π.hist ω k).elapsed

/-- The time at which the `(k+1)`th job served is completed. -/
def Policy.completionTime (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) : ℝ := (π.hist ω (k + 1)).elapsed

/-- The number of jobs not in the set `A` of completed jobs. -/
def numRemaining (A : Finset (Fin n)) : ℕ := n - A.card

/-- Job `j` is available for service when the set of completed jobs is `B`: it is not completed
and all its predecessors are. -/
def IsAvailable (F : JobFamily n) (B : Finset (Fin n)) (j : Fin n) : Prop :=
  j ∉ B ∧ ∀ i, F.prec i j → i ∈ B

/-- A policy is feasible from the initial set `A` of completed jobs if, for every realization of
the service times, each job it starts is available (uncompleted, all predecessors completed),
until every job is completed. -/
def Policy.Feasible (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n) : Prop :=
  ∀ (ω : Fin n → ℝ) (k : ℕ), k < numRemaining A →
    IsAvailable F (A ∪ (π.hist ω k).jobs) (π.job ω k)

/-- The payoff `R_π(𝓕) = E ∑_i V_i e^{−γ C_i}` of a policy from the initial set `A` of completed
jobs, the sum over the jobs not in `A`. -/
noncomputable def Policy.payoff (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range (numRemaining A),
      F.reward (π.job ω k) * Real.exp (-F.γ * π.completionTime ω k) ∂serviceLaw F

/-- An optimal policy from the initial set `A`: feasible, and its payoff is at least that of every
feasible policy. -/
def IsOptimalPolicy (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n) : Prop :=
  π.Feasible F A ∧ ∀ g : Policy n, g.Feasible F A → g.payoff F A ≤ π.payoff F A

/-- A stage `(g, τ)`: a policy `g` together with a positive stopping time `τ`. After each
completion the stage ends if `stop h = true`, `h` the history since the stage began; it ends in any
case when every job is completed. At least one job is served (`τ > 0`). -/
structure Stage (n : ℕ) extends Policy n where
  /-- Whether the stage ends after the history `h` (checked after each completion). -/
  stop : History n → Bool
  measurable_stop : ∀ k : ℕ, Measurable fun h : Fin k → Fin n × ℝ => stop (List.ofFn h)

/-- The stage is feasible from `B`: its policy is. -/
def Stage.Feasible (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) : Prop :=
  p.toPolicy.Feasible F B

/-- The `(k+1)`th job served by the stage started from the set `B` of completed jobs is served
before the stage ends: `k < numRemaining B` and the stage did not end after `1, …, k`
completions. -/
def Stage.InStage (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) (k : ℕ) : Prop :=
  k < numRemaining B ∧ ∀ l ∈ Finset.Icc 1 k, p.stop (p.toPolicy.hist ω l) = false

open Classical in
/-- `R_{gτ}(𝓕)`: the expected discounted reward of the stage from the set `B` of completed jobs. -/
noncomputable def Stage.reward (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if p.InStage B ω k then
        F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k)
      else 0) ∂serviceLaw F

open Classical in
/-- `W_{gτ}(𝓕)`: the expected discounted time of the stage from the set `B`,
`E ∫_0^{T} e^{−γ t} dt = γ⁻¹ E(1 − e^{−γ T})`, `T` the time at which the stage ends. -/
noncomputable def Stage.time (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k))
      else 0) ∂serviceLaw F

/-- The ratio `R_{gτ}(𝓕) / W_{gτ}(𝓕)`. -/
noncomputable def Stage.ratio (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) : ℝ :=
  p.reward F B / p.time F B

/-- The index (4.15) of the family when the set of completed jobs is `B`:
`ν(𝓕) = sup_{g, τ} R_{gτ}(𝓕) / W_{gτ}(𝓕)`, over all feasible stages. -/
noncomputable def familyIndex (F : JobFamily n) (B : Finset (Fin n)) : ℝ :=
  sSup {x : ℝ | ∃ p : Stage n, p.Feasible F B ∧ x = p.ratio F B}

/-- The first stage `(π, σ)` of a modified forwards induction (FI*) policy from `B`: a feasible
stage attaining the supremum in (4.15). -/
def IsFIStarStage (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n) : Prop :=
  p.Feasible F B ∧ p.ratio F B = familyIndex F B

/-- A static stage: its choices and its stopping decisions depend only on the number of jobs
completed in the stage, not on their service times; it serves a fixed set of jobs in a fixed
order. -/
def Stage.IsStatic (p : Stage n) : Prop :=
  ∀ l l' : History n, l.length = l'.length → p.next l = p.next l' ∧ p.stop l = p.stop l'

open Classical in
/-- The set of jobs completed during the stage `p` from `B` when the service times are `ω`. -/
noncomputable def Stage.jobsDone (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) :
    Finset (Fin n) :=
  ((Finset.range (numRemaining B)).filter (p.InStage B ω)).image (p.toPolicy.job ω)

open Classical in
/-- `R_{gπσ}(𝓕)`: the expected discounted reward accruing under the policy `g` (from `B`) to the
jobs that would have been completed during the stage `(π, σ) = p`, had it been employed (same
service times). -/
noncomputable def postponedReward (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n)
    (g : Policy n) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if g.job ω k ∈ p.jobsDone B ω then
        F.reward (g.job ω k) * Real.exp (-F.γ * g.completionTime ω k)
      else 0) ∂serviceLaw F

open Classical in
/-- `W_{gπσ}(𝓕)`: the expected discounted time accruing under the policy `g` (from `B`) to the
jobs that would have been completed during the stage `(π, σ) = p`: for each such job,
`∫_{S_i}^{C_i} e^{−γ t} dt`, `S_i, C_i` its start and completion times under `g`. -/
noncomputable def postponedTime (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n)
    (g : Policy n) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if g.job ω k ∈ p.jobsDone B ω then
        F.γ⁻¹ * (Real.exp (-F.γ * g.startTime ω k) - Real.exp (-F.γ * g.completionTime ω k))
      else 0) ∂serviceLaw F

/-- Running stages one after another: `ρ h₀` is the stage begun after the history `h₀`. The state
after `k` completions is `(h₀, l)`: `h₀` the history at which the current stage began, `l` the
history since then. When the current stage ends, a new one begins. -/
def stagedState (ρ : History n → Stage n) (ω : Fin n → ℝ) : ℕ → History n × History n
  | 0 => ([], [])
  | k + 1 =>
    let s := stagedState ρ ω k
    let j := (ρ s.1).next s.2
    let l := s.2 ++ [(j, ω j)]
    if (ρ s.1).stop l then (s.1 ++ l, []) else (s.1, l)

/-- The `(k+1)`th job served when stages are run one after another by `ρ`. -/
def stagedJob (ρ : History n → Stage n) (ω : Fin n → ℝ) (k : ℕ) : Fin n :=
  (ρ (stagedState ρ ω k).1).next (stagedState ρ ω k).2

/-- A modified forwards induction (FI*) policy from `A` (§2.6.6, §4.6): it repeatedly begins a
stage that attains the index (4.15) of the current family (the set of completed jobs being
`A ∪ h.jobs`) and follows it until it ends; equivalently, it agrees almost surely with the
staged policy of a rule `ρ` choosing an FI* first stage after every history. -/
def IsFIStarPolicy (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n) : Prop :=
  π.Feasible F A ∧ ∃ ρ : History n → Stage n,
    (∀ h : History n, A ∪ h.jobs ≠ Finset.univ → IsFIStarStage F (A ∪ h.jobs) (ρ h)) ∧
    ∀ᵐ ω ∂serviceLaw F, ∀ k < numRemaining A, π.job ω k = stagedJob ρ ω k

/-- A forwards induction (FI) policy from `A` (§2.6.6): almost surely, at every decision time it
starts a job with which some FI* first stage of the current family begins. -/
def IsFIPolicy (F : JobFamily n) (A : Finset (Fin n)) (π : Policy n) : Prop :=
  π.Feasible F A ∧ ∀ᵐ ω ∂serviceLaw F, ∀ k < numRemaining A,
    ∃ p : Stage n, IsFIStarStage F (A ∪ (π.hist ω k).jobs) p ∧ p.next [] = π.job ω k

/-- An ε-FI* policy from `A` (§4.10): like an FI* policy, but each stage is only required to have
ratio at least `ν(𝓕) − ε`, `ν(𝓕)` the index (4.15) of the family when the stage begins. -/
def IsEpsFIStarPolicy (F : JobFamily n) (A : Finset (Fin n)) (ε : ℝ) (π : Policy n) : Prop :=
  π.Feasible F A ∧ ∃ ρ : History n → Stage n,
    (∀ h : History n, A ∪ h.jobs ≠ Finset.univ →
      (ρ h).Feasible F (A ∪ h.jobs) ∧
        familyIndex F (A ∪ h.jobs) - ε ≤ (ρ h).ratio F (A ∪ h.jobs)) ∧
    ∀ᵐ ω ∂serviceLaw F, ∀ k < numRemaining A, π.job ω k = stagedJob ρ ω k

end AllocationIndices.Precedence


