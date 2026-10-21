-- Prove2me | Definitions.Def_AllocationIndices_Freezing_Model
-- name    : AllocationIndices_Freezing_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:01.28546+00:00
-- url     : https://prove2.me/theorems/8602a37c-7e9a-442c-b8bb-802e894b292c
-- title:
--   Freezing rules, the index of a family of bandit processes, and ε-index* policies (§4.5, §4.10)
-- statement:
--   The objects of §4.5 and §4.10, in the discrete-time model of the series: a **bandit process** $B$ is a Markov chain $x(0), x(1), \dots$ on a state space $S$ with transition kernel $P$, it yields the reward $r(x(t))$ each time the continuation control is applied, and rewards are discounted by $a^t$ with $0 < a < 1$. $\nu(B, x)$ is the Gittins index (2.6) of $B$ in state $x$, $R_\tau, W_\tau, \nu_\tau = R_\tau / W_\tau$ are the expected discounted reward, the expected discounted time and their ratio up to a stopping time $\tau$ (2.7), all from the published definitions of the series.
--
--   1. **Freezing rules** (§4.5.1, p. 93). A freezing rule $f$ for $B$ is a sequence $f_0 \le f_1 \le f_2 \le \cdots$ with values in $\{0, 1, 2, \dots\} \cup \{\infty\}$, where $f_i$ is the total time for which $B$ has been frozen before the continuation control is applied to it for the $(i+1)$th time, i.e. at process time $i$; $f_i$ is a function of the trajectory of $B$ that depends only on $x(0), \dots, x(i)$, and $f_i = \infty$ means that $B$ is never continued again. The reward $r(x(i))$ then accrues at time $i + f_i$. With $a^\infty = 0$,
--   $$R_f(B, x) = E\Big[\sum_{i \ge 0} a^{i + f_i}\, r(x(i)) \,\Big|\, x(0) = x\Big], \qquad W_f(B, x) = E\Big[\sum_{i \ge 0} a^{i + f_i} \,\Big|\, x(0) = x\Big],$$
--   and $\nu_f(B, x) = R_f(B, x) / W_f(B, x)$.
--
--   2. **The index of a family** (Eq. (4.5), p. 90). A simple family $F$ of $k$ alternative bandit processes is operated by a policy $g$ that at each decision time $t = 0, 1, 2, \dots$ continues one of the $k$ bandits, chosen (possibly at random) on the basis of the history: the state-vectors observed so far and the bandits continued so far; only the continued bandit changes state. A **positive stopping time** $\tau$ of the family is a rule deciding, at each decision time $n$ and from the history up to $n$, whether $\tau > n$; it satisfies $\tau > 0$, and $\tau > n + 1$ implies $\tau > n$. From the initial state-vector $x$,
--   $$R_{g\tau}(F, x) = \sum_{t \ge 0} a^t\, E_g\big[r(\text{state of the bandit continued at } t);\ \tau > t\big], \qquad W_{g\tau}(F, x) = \sum_{t \ge 0} a^t\, P_g(\tau > t),$$
--   and the index of the family is
--   $$\nu(F, x) = \sup_{g, \tau} \frac{R_{g\tau}(F, x)}{W_{g\tau}(F, x)},$$
--   the supremum over all policies $g$ and positive stopping times $\tau$.
--
--   3. **ε-index\* policies** (§4.10, pp. 111–112). A staged rule specifies, at the start of a stage at decision time $m$ and as a function of the state-vectors $y(0), \dots, y(m)$ observed so far, a bandit $B$ to continue and a stopping time $\tau$ of $B$'s own trajectory from its current state. The stage lasts $\tau$ decision times (forever if $\tau = \infty$); then a new stage starts. The rule satisfies the **ε-index\* condition** if at the start of every stage $\tau$ is a positive stopping time and
--   $$\nu_\tau(B) \ge \max_j \nu(B_j) - \varepsilon,$$
--   all indices being evaluated at the current states. A policy $h$ is an **ε-index\* policy** if, for some staged rule satisfying the ε-index\* condition, at every decision time and after every history $h$ continues, with probability one, the bandit the rule prescribes.
--
--   **Formalization Note** Time is discrete: decision times are $0, 1, 2, \dots$, so the book's $\int_{t_i}^{t_{i+1}} a^t\,dt$ in $W_f$ becomes $a^{i}$ for the process time interval $[i, i+1)$, and every index here is the discrete-time index (2.6), whose denominator is $E\sum_{t<\tau} a^t$. A family of bandit processes is $k$ copies of one kernel `P` and reward `r` on a common state space (different bandits are the disjoint-union special case, §2.9), as in the published `MarkovBanditPolicy`; the family's value under a policy is the published `markovBanditDiscountedValue`. The stopping time of a family is a Boolean "still running" flag on histories; on a countable state space every such flag is past-measurable. An ε-index\* policy is required to follow its staged rule after every history, including histories of probability zero, and its stage choices are deterministic functions of the observed state-vectors; every policy with the book's property agrees almost surely with one of this form.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.5 p. 90 (Eq. (4.5)), p. 91 (Eq. (4.8)), §4.5.1 p. 93 (freezing rules), §4.10 pp. 111–112 (ε-index* policies)

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
§4.5 (pp. 90–96) and §4.10 (pp. 111–112): freezing rules, the index of a family of alternative
bandit processes, and ε-index* policies, in the discrete-time model of the series
(`Def_GittinsIndex`, `Def_AllocationIndices_Index`): a bandit process is a Markov chain with
kernel `P` and reward `r` on a state space `S`, decision times are `0, 1, 2, …`, rewards are
discounted by `a^t`, and `gittinsIndex P r a x` is the index (2.6).

* `FreezingRule S` — a freezing rule (§4.5.1, p. 93): `freeze i ω = f_i`, the total time for
  which `B` has been frozen before the continuation control is applied to it for the `(i+1)`th
  time (at process time `i`), as a function of the trajectory `ω` of `B`. The `f_i` are
  nondecreasing, take values in `{0, 1, 2, …} ∪ {∞}` (`f_i = ∞`: `B` is never continued again)
  and `f_i` depends only on the history `ω 0, …, ω i` of `B` up to process time `i`.
* `freezingReward`, `freezingTime`, `freezingRatio` — `R_f(B) = E ∑_i a^{i + f_i} r(x(i))`,
  `W_f(B) = E ∑_i a^{i + f_i}` (the discrete-time form of `E ∑_i a^{f_i} ∫_{t_i}^{t_{i+1}} a^t dt`,
  Eq. (4.8)), and `ν_f(B) = R_f(B) / W_f(B)`; `a^∞ = 0`.
* `FamilyStoppingTime k T`, `familyStoppedReward`, `familyStoppedTime`, `familyIndex` — for a
  simple family of `k` alternative bandit processes (one kernel on a common state space, as in
  `MarkovBanditPolicy`), a positive stopping time of the family's history, `R_{gτ}(F)`,
  `W_{gτ}(F)` under a policy `g`, and the family index (4.5)
  `ν(F) = sup_{g, τ} R_{gτ}(F) / W_{gτ}(F)`.
* `StageRule`, `StageRule.IsEpsIndexStar`, `IsEpsIndexStarPolicy` — ε-index* policies (§4.10,
  pp. 111–112): the policy proceeds in stages; at the start of each stage it chooses a bandit `B`
  and a positive stopping time `τ` of `B`'s own evolution with `ν_τ(B) ≥ max_j ν(B_j) − ε`
  (indices at the current states), continues `B` for `τ` decision times, and repeats.
-/

namespace AllocationIndices.Freezing

/-! ### Freezing rules for a single bandit process -/

/-- `a^n` for `n ∈ {0, 1, 2, …} ∪ {∞}`, with `a^∞ = 0` (a reward that never accrues). -/
noncomputable def discountPow (a : ℝ) : ℕ∞ → ℝ
  | ⊤ => 0
  | (n : ℕ) => a ^ n

/-- A freezing rule for a bandit process on `S` (§4.5.1, p. 93). `freeze i ω = f_i` is the total
freeze time applied before the continuation control is applied for the `(i+1)`th time, i.e. the
reward `r(ω i)` of process time `i` accrues at time `i + f_i`. The sequence is nondecreasing
(freeze periods `f_i − f_{i−1} ≥ 0` are inserted just before each continuation), `f_i = ⊤` means
that `B` is never continued again, and `f_i` depends only on the history `ω 0, …, ω i` of `B` up
to process time `i`. -/
structure FreezingRule (S : Type*) [MeasurableSpace S] where
  /-- `f_i` as a function of the trajectory of `B`. -/
  freeze : ℕ → (ℕ → S) → ℕ∞
  /-- `f_0 ≤ f_1 ≤ f_2 ≤ ⋯`. -/
  mono : ∀ i ω, freeze i ω ≤ freeze (i + 1) ω
  /-- `f_i` is determined by `ω 0, …, ω i`. -/
  adapted : ∀ (i n : ℕ), MeasurableSet[trajectoryFiltration S i] {ω | freeze i ω ≤ (n : ℕ∞)}

variable {S : Type*} [MeasurableSpace S]

/-- `R_f(B, x) = E[∑_{i ≥ 0} a^{i + f_i} r(x(i)) | x(0) = x]` (Eq. (4.8)): the expected discounted
reward from `B` started in `x` under the freezing rule `f`. -/
noncomputable def freezingReward (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ)
    (f : FreezingRule S) (x : S) : ℝ :=
  ∫ ω, ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * r (ω i) ∂markovChainMeasure P x

/-- `W_f(B, x) = E[∑_{i ≥ 0} a^{i + f_i} | x(0) = x]` (Eq. (4.8), discrete time: the process
time interval `[i, i + 1)`, postponed by `f_i`, contributes discounted time `a^{i + f_i}`). -/
noncomputable def freezingTime (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (f : FreezingRule S)
    (x : S) : ℝ :=
  ∫ ω, ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) ∂markovChainMeasure P x

/-- `ν_f(B, x) = R_f(B, x) / W_f(B, x)` (p. 93). -/
noncomputable def freezingRatio (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (a : ℝ)
    (f : FreezingRule S) (x : S) : ℝ :=
  freezingReward P r a f x / freezingTime P a f x

/-! ### The index of a simple family of alternative bandit processes -/

variable {T : Type*} [MeasurableSpace T] {k : ℕ}

/-- The history of the first `n` decision times, read off a history of `n + 1` decision times:
the first `n` (state-vector, bandit continued) pairs, and the state-vector at decision time `n`. -/
def historyInit {n : ℕ} (h : MarkovBanditHistory k T (n + 1)) : MarkovBanditHistory k T n :=
  (fun j ↦ h.1 j.castSucc, (h.1 (Fin.last n)).1)

/-- A positive stopping time `τ` of a family of `k` bandit processes: `cont n h = true` means
`τ > n`, i.e. the family is still being operated at decision time `n`, decided from the history
`h` up to decision time `n` (past state-vectors, the bandits continued, current state-vector).
`τ ≥ 1`, and once stopped the family stays stopped. -/
structure FamilyStoppingTime (k : ℕ) (T : Type*) where
  /-- `cont n h = true` iff `τ > n`. -/
  cont : (n : ℕ) → MarkovBanditHistory k T n → Bool
  /-- `τ > 0`. -/
  cont_zero : ∀ h, cont 0 h = true
  /-- `τ > n + 1` implies `τ > n`. -/
  cont_mono : ∀ (n : ℕ) (h : MarkovBanditHistory k T (n + 1)),
    cont (n + 1) h = true → cont n (historyInit h) = true

/-- `R_{gτ}(F, x)`: the expected discounted reward accrued by the family started in the
state-vector `x` under policy `g` before the stopping time `τ`,
`∑_t a^t E[r(state of the bandit continued at t); τ > t]`. -/
noncomputable def familyStoppedReward (P : Kernel T T) [IsMarkovKernel P] (r : T → ℝ) (a : ℝ)
    (g : MarkovBanditPolicy k T) (τ : FamilyStoppingTime k T) (x : Fin k → T) : ℝ :=
  ∑' t : ℕ, a ^ t * ∫ h, (if τ.cont t (historyInit h) = true then
      r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)) else 0) ∂markovBanditMeasure P g x (t + 1)

/-- `W_{gτ}(F, x) = ∑_t a^t P(τ > t)`: the expected discounted time before `τ`. -/
noncomputable def familyStoppedTime (P : Kernel T T) [IsMarkovKernel P] (a : ℝ)
    (g : MarkovBanditPolicy k T) (τ : FamilyStoppingTime k T) (x : Fin k → T) : ℝ :=
  ∑' t : ℕ, a ^ t * ∫ h, (if τ.cont t (historyInit h) = true then (1 : ℝ) else 0)
    ∂markovBanditMeasure P g x (t + 1)

/-- The index of the family (4.5), `ν(F, x) = sup_{g, τ} R_{gτ}(F, x) / W_{gτ}(F, x)`, the
supremum over all policies `g` and positive stopping times `τ`. -/
noncomputable def familyIndex (P : Kernel T T) [IsMarkovKernel P] (r : T → ℝ) (a : ℝ)
    (x : Fin k → T) : ℝ :=
  sSup {v : ℝ | ∃ (g : MarkovBanditPolicy k T) (τ : FamilyStoppingTime k T),
    v = familyStoppedReward P r a g τ x / familyStoppedTime P a g τ x}

/-! ### ε-index* policies -/

/-- The state-vector at decision time `t` recorded in a history of `n` decision times (for
`t ≥ n`, the current state-vector). -/
def stateAt {n : ℕ} (h : MarkovBanditHistory k T n) (t : ℕ) : Fin k → T :=
  if ht : t < n then (h.1 ⟨t, ht⟩).1 else h.2

/-- The state-vectors at decision times `0, …, m` recorded in a history. -/
def statePath {n : ℕ} (h : MarkovBanditHistory k T n) (m : ℕ) : Fin (m + 1) → Fin k → T :=
  fun j ↦ stateAt h j

/-- The states of bandit `i` at decision times `s, s + 1, s + 2, …` recorded in a history (its
trajectory since decision time `s`; constant after the end of the history). -/
def armPath {n : ℕ} (h : MarkovBanditHistory k T n) (i : Fin k) (s : ℕ) : ℕ → T :=
  fun u ↦ stateAt h (s + u) i

/-- The choices of a staged policy: at the start of a stage at decision time `m`, given the
state-vectors `y 0, …, y m` observed so far, the bandit `arm m y` to continue and the stopping
time `stop m y` (a function of that bandit's trajectory from its current state `y m (arm m y)`)
at which the stage ends. -/
structure StageRule (k : ℕ) (T : Type*) where
  /-- The bandit chosen at the start of a stage. -/
  arm : (m : ℕ) → (Fin (m + 1) → Fin k → T) → Fin k
  /-- The stopping time ending the stage, on the chosen bandit's own trajectory. -/
  stop : (m : ℕ) → (Fin (m + 1) → Fin k → T) → (ℕ → T) → ℕ∞

/-- The ε-index* condition (§4.10, p. 111): at the start of every stage, the stopping time is a
positive stopping time of the chosen bandit `B` and `ν_τ(B) ≥ max_j ν(B_j) − ε`, all indices
being evaluated at the current states. -/
def StageRule.IsEpsIndexStar (ρ : StageRule k T) (P : Kernel T T) [IsMarkovKernel P]
    (r : T → ℝ) (a ε : ℝ) : Prop :=
  ∀ (m : ℕ) (y : Fin (m + 1) → Fin k → T),
    IsPositiveStoppingTime (ρ.stop m y) ∧
    ∀ j : Fin k, gittinsIndex P r a (y (Fin.last m) j) - ε ≤
      stoppedRatio P r a (ρ.stop m y) (y (Fin.last m) (ρ.arm m y))

/-- The stage in progress at decision time `t` along a history: its starting decision time and
the bandit it continues. Stage `0` starts at time `0`; a stage started at `s` with bandit `i` and
stopping time `τ` is still in progress at time `t + 1` iff `t + 1 − s < τ` evaluated on the
trajectory of bandit `i` since `s`; otherwise a new stage starts at `t + 1`. -/
def StageRule.stage (ρ : StageRule k T) {n : ℕ} (h : MarkovBanditHistory k T n) :
    ℕ → ℕ × Fin k
  | 0 => (0, ρ.arm 0 (statePath h 0))
  | t + 1 =>
    if (((t + 1 - (ρ.stage h t).1 : ℕ)) : ℕ∞) <
        ρ.stop (ρ.stage h t).1 (statePath h (ρ.stage h t).1)
          (armPath h (ρ.stage h t).2 (ρ.stage h t).1) then ρ.stage h t
    else (t + 1, ρ.arm (t + 1) (statePath h (t + 1)))

/-- The bandit that the staged policy continues at the current decision time `n` of a history of
`n` decision times. -/
def StageRule.prescribedArm (ρ : StageRule k T) {n : ℕ} (h : MarkovBanditHistory k T n) : Fin k :=
  (ρ.stage h n).2

/-- An ε-index* policy (§4.10, pp. 111–112): a policy that, at every decision time and after every
history, continues (with probability one) the bandit prescribed by a staged rule satisfying the
ε-index* condition at the start of every stage. -/
def IsEpsIndexStarPolicy (P : Kernel T T) [IsMarkovKernel P] (r : T → ℝ) (a ε : ℝ)
    (π : MarkovBanditPolicy k T) : Prop :=
  ∃ ρ : StageRule k T, ρ.IsEpsIndexStar P r a ε ∧
    ∀ (n : ℕ) (h : MarkovBanditHistory k T n), (π.select n) h {ρ.prescribedArm h} = 1

end AllocationIndices.Freezing


