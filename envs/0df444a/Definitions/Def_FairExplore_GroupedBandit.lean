-- Prove2me | Definitions.Def_FairExplore_GroupedBandit
-- name    : FairExplore_GroupedBandit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:04.54274+00:00
-- url     : https://prove2.me/theorems/68c8a951-5eff-47e2-8507-1407d2b54324
-- title:
--   Grouped bandit with fixed action sets: arrivals, reward stacks, policies, runs and group regret
-- statement:
--   A **grouped bandit with fixed action sets** consists of a finite set of groups $G$, a finite set of arms $\mathcal A$, the set $\mathcal A^g\subseteq\mathcal A$ of arms available to group $g$, and arrival probabilities $p_g\ge 0$ with $\sum_g p_g=1$. Each arm $a$ has an i.i.d. reward sequence $(Y_n(a))_{n\ge1}$ with law $\nu_a$ and mean $\theta(a)$.
--
--   1. **Probability space.** The arriving groups $g_1,g_2,\dots$ are i.i.d. with $\Pr(g_t=g)=p_g$; the reward stacks of the arms are independent i.i.d. sequences; the policy's own randomness is an i.i.d. sequence $U_1,U_2,\dots$ uniform on $[0,1]$; the three families are independent.
--   2. **Policy.** At time $t$ a policy sees the groups, arms and rewards of times $1,\dots,t-1$, the arriving group $g_t$ and its draw $U_t$, and returns an arm $A_t$. It is *admissible* if $A_t\in\mathcal A^{g_t}$ whenever $\mathcal A^{g_t}\neq\emptyset$, and *measurable* if the arm it returns is a Borel function of the past rewards and $U_t$.
--   3. **Run.** The reward of the pull at time $t$ is the next unused entry of the stack: $Y_t=Y_{N_t(A_t)+1}(A_t)$, where $N_t(a)$ is the number of pulls of $a$ before time $t$. $N^g_T(a)$ counts the pulls of $a$ by group $g$ in times $1,\dots,T$, and $\mathrm{Arr}^g_T$ the arrivals of $g$; $\hat\theta_t(a)$ is the empirical mean of the rewards of $a$ before time $t$.
--   4. **Regret.** With $\mathrm{OPT}(g)=\max_{a\in\mathcal A^g}\theta(a)$,
--   $$R^g_T(\pi,\mathcal I)=\mathbb E\Big[\sum_{t=1}^T \mathbf 1(g_t=g)\big(\mathrm{OPT}(g_t)-\theta(A_t)\big)\Big],\qquad R_T(\pi,\mathcal I)=\sum_{g}R^g_T(\pi,\mathcal I).$$
--
--   This is the grouped bandit model of §2.1 in the case where the law $P^g$ of the action set is the unit mass on $\mathcal A^g$; it covers both the grouped $K$-armed bandit (§2.4.1) and the single-group instances $\mathcal I_g$ of §2.3 used for the disagreement point.
--
--   **Formalization Note** Lean step $s$ is paper time $t=s+1$; the history after $s$ steps is a `History` with $s$ entries. Reward stacks are indexed from $0$, so the $(n+1)$-th pull of arm $a$ receives `ω.2.1 a n`. The empirical mean of an unpulled arm is $0$ (the paper leaves it unspecified). Expectations are lower Lebesgue integrals `∫⁻` of nonnegative quantities, so no integrability condition is needed and no value collapses to $0$. The policy's randomness is an input $U_t\in[0,1]$ rather than an internal coin.
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, §2.1, pp.6–7; §2.4.1, p.9; Pull and Arr notation, pp.32, 34

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FairExplore

/-- The known structure of a grouped bandit with fixed action sets: a finite set of groups `γ`,
the arms `A g ⊆ α` available to group `g`, and the arrival probabilities `p g ≥ 0` with
`∑_g p_g = 1`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, §2.1, p.6 and
§2.4.1, p.9 ("For each g, P^g places unit mass on A^g").

**Formalization Note** The distribution `P^g` over action sets of §2.1 is the unit mass on `A g`,
which is the grouped K-armed model of §2.4.1 and also the single-group instances `I_g` of §2.3.
The structure keeps `p g ≥ 0` as printed; theorems that need `p g > 0` assume it. -/
structure GroupedStructure (γ α : Type*) [Fintype γ] where
  /-- `A g`: the arms available to group `g` (`A^g`, p.9). -/
  A : γ → Finset α
  /-- `p g`: the arrival probability of group `g` (p.6). -/
  p : γ → ℝ
  p_nonneg : ∀ g, 0 ≤ p g
  p_sum : ∑ g, p g = 1

variable {γ α : Type*}

/-- The arrival law of the groups, `Pr(g_t = g) = p_g` (p.6). -/
noncomputable def GroupedStructure.arrivalPMF [Fintype γ] (S : GroupedStructure γ α) : PMF γ :=
  PMF.ofFintype (fun g => ENNReal.ofReal (S.p g)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => S.p_nonneg g), S.p_sum, ENNReal.ofReal_one])

/-- The sample space of a grouped bandit run (p.6–7): the arrival sequence `g_t`, the reward stacks
`Y_n(a)` of every arm, and the policy's own randomness `U_t ∈ [0,1]`.
Coordinates: `ω.1 t` is the group arriving at step `t` (paper time `t + 1`); `ω.2.1 a n` is the
reward `Y_{n+1}(a)` of the `(n+1)`-th pull of arm `a`; `ω.2.2 t` is `U_t`. -/
abbrev Outcome (γ α : Type*) := (ℕ → γ) × (α → ℕ → ℝ) × (ℕ → unitInterval)

/-- The law of a run (p.6–7: "the expectation is over randomness in arrivals (g_t, A_t), rewards
Y_n(a), and the policy π"): the arrivals are i.i.d. with law `p`, the rewards `(Y_n(a))_{n ≥ 1}` of
each arm are i.i.d. with law `ν a`, the policy's draws `U_t` are i.i.d. uniform on `[0,1]`, and the
three families are independent.

**Formalization Note** The reward-stack model of p.6 (`Y_t = Y_{N_t(A_t)+1}(A_t)`) is used as
printed. Expectations against this law are `∫⁻` of nonnegative quantities. -/
noncomputable def law [Fintype γ] [MeasurableSpace γ] (S : GroupedStructure γ α)
    (ν : α → Measure ℝ) [∀ a, IsProbabilityMeasure (ν a)] : Measure (Outcome γ α) :=
  (Measure.infinitePi fun _ : ℕ => S.arrivalPMF.toMeasure).prod
    ((Measure.infinitePi fun a : α => Measure.infinitePi fun _ : ℕ => ν a).prod
      (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))

/-- A (randomized, non-anticipating) policy (p.6): at step `t` (paper time `t + 1`) it sees the
groups, arms and rewards of the `t` earlier steps, the arriving group `g_t` and its own uniform
draw `U_t`, and returns the arm to pull. One policy is one rule for every parameter `θ`: it knows
the structure `(A, G, p)` but not `θ` (p.6, "all quantities except for θ are known"). -/
def Policy (γ α : Type*) : Type _ :=
  (t : ℕ) → (Fin t → γ) → (Fin t → α) → (Fin t → ℝ) → γ → unitInterval → α

/-- The observations of the first `t` steps: the arriving groups, the pulled arms, the rewards. -/
structure History (γ α : Type*) (t : ℕ) where
  groups : Fin t → γ
  arms : Fin t → α
  rewards : Fin t → ℝ

/-- `N(a)`: the number of pulls of arm `a` in the history. -/
def History.count [DecidableEq α] {t : ℕ} (h : History γ α t) (a : α) : ℕ :=
  (Finset.univ.filter fun i => h.arms i = a).card

/-- `N^g(a)`: the number of pulls of arm `a` by group `g` in the history. -/
def History.gcount [DecidableEq γ] [DecidableEq α] {t : ℕ} (h : History γ α t) (g : γ)
    (a : α) : ℕ :=
  (Finset.univ.filter fun i => h.groups i = g ∧ h.arms i = a).card

/-- `θ̂(a)`: the empirical mean of the rewards of arm `a` in the history; `0` for an arm that has
never been pulled (the paper leaves that value unspecified). -/
noncomputable def History.mean [DecidableEq α] {t : ℕ} (h : History γ α t) (a : α) : ℝ :=
  if h.count a = 0 then 0
  else (∑ i ∈ Finset.univ.filter (fun i => h.arms i = a), h.rewards i) / h.count a

/-- The history of a run of policy `π` on outcome `ω` after `t` steps. At step `t` the group
`g_t = ω.1 t` arrives, the policy pulls `A_t = π_t(history, g_t, U_t)`, and the reward is the next
unused entry of `A_t`'s stack: `Y_t = Y_{N_t(A_t)+1}(A_t)` (p.6), i.e. stack index `N_t(A_t)`
counted from `0`. -/
noncomputable def hist [DecidableEq α] (π : Policy γ α) (ω : Outcome γ α) :
    (t : ℕ) → History γ α t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 =>
    let h := hist π ω t
    let a := π t h.groups h.arms h.rewards (ω.1 t) (ω.2.2 t)
    ⟨Fin.snoc (α := fun _ => γ) h.groups (ω.1 t), Fin.snoc (α := fun _ => α) h.arms a,
      Fin.snoc (α := fun _ => ℝ) h.rewards (ω.2.1 a (h.count a))⟩

/-- `A_t`: the arm pulled at step `t` (paper time `t + 1`). -/
noncomputable def arm [DecidableEq α] (π : Policy γ α) (ω : Outcome γ α) (t : ℕ) : α :=
  π t (hist π ω t).groups (hist π ω t).arms (hist π ω t).rewards (ω.1 t) (ω.2.2 t)

/-- `N_T(a)`: the number of pulls of arm `a` in steps `0, …, T − 1` (paper times `1, …, T`).
At step `t` this is the paper's `N_{t+1}(a)`, "the total number of times arm a was pulled up to but
not including time t + 1" (p.6). -/
noncomputable def N [DecidableEq α] (π : Policy γ α) (ω : Outcome γ α) (T : ℕ) (a : α) : ℕ :=
  (hist π ω T).count a

/-- `N^g_T(a)`: the number of pulls of arm `a` by group `g` in steps `0, …, T − 1` (p.9). -/
noncomputable def gN [DecidableEq γ] [DecidableEq α] (π : Policy γ α) (ω : Outcome γ α) (T : ℕ)
    (g : γ) (a : α) : ℕ :=
  (hist π ω T).gcount g a

/-- `Arr^g_T = ∑_{s=1}^T 1(g_s = g)`: the number of arrivals of group `g` in paper times
`1, …, T` (p.34). -/
def arrivals [DecidableEq γ] (ω : Outcome γ α) (T : ℕ) (g : γ) : ℕ :=
  ((Finset.range T).filter fun s => ω.1 s = g).card

/-- `OPT(g) = max_{a ∈ A^g} θ(a)`: the best mean available to group `g` (p.9), for a vector of means
`θ`; `0` if `A g` is empty (a case the theorems exclude). -/
noncomputable def opt (A : γ → Finset α) (θ : α → ℝ) (g : γ) : ℝ :=
  if h : (A g).Nonempty then (A g).sup' h θ else 0

/-- The group regret `R^g_T(π, I) = E[∑_{t=1}^T 1(g_t = g)(µ(A*_t) − µ(A_t))]` (p.6) of policy `π`
in the grouped bandit with structure `S`, reward laws `ν` and means `θ` (`θ a` is the mean of
`ν a`), where `µ(A*_t) = OPT(g_t)` because the available set is `A^{g_t}`.

**Formalization Note** The expectation is the `∫⁻` of a nonnegative integrand (the gap of an
admissible pull is `≥ 0`), finite because the integrand is at most `T · max gap`. -/
noncomputable def groupRegret [Fintype γ] [MeasurableSpace γ] [DecidableEq γ] [DecidableEq α]
    (S : GroupedStructure γ α) (ν : α → Measure ℝ) [∀ a, IsProbabilityMeasure (ν a)]
    (θ : α → ℝ) (π : Policy γ α) (T : ℕ) (g : γ) : ℝ :=
  (∫⁻ ω, ∑ s ∈ Finset.range T,
      (if ω.1 s = g then ENNReal.ofReal (opt S.A θ g - θ (arm π ω s)) else 0) ∂(law S ν)).toReal

/-- The total regret `R_T(π, I) = ∑_g R^g_T(π, I)` (p.6). -/
noncomputable def regret [Fintype γ] [MeasurableSpace γ] [DecidableEq γ] [DecidableEq α]
    (S : GroupedStructure γ α) (ν : α → Measure ℝ) [∀ a, IsProbabilityMeasure (ν a)]
    (θ : α → ℝ) (π : Policy γ α) (T : ℕ) : ℝ :=
  ∑ g, groupRegret S ν θ π T g

/-- A policy is admissible for the action sets `A` when it always pulls an arm available to the
arriving group: "chooses an arm A_t ∈ A_t to pull" (p.6), with `A_t = A^{g_t}` (p.9). -/
def IsAdmissible (A : γ → Finset α) (π : Policy γ α) : Prop :=
  ∀ t gs as ys g u, (A g).Nonempty → π t gs as ys g u ∈ A g

/-- A policy is measurable when, for every step, every record of past groups and arms, every
arriving group and every arm, the set of (past rewards, own draw) leading to that arm is Borel.
The groups and arms are finite, so this is joint measurability of the policy. -/
def IsMeasurablePolicy (π : Policy γ α) : Prop :=
  ∀ t (gs : Fin t → γ) (as : Fin t → α) (g : γ) (a : α),
    MeasurableSet {x : (Fin t → ℝ) × unitInterval | π t gs as x.1 g x.2 = a}

end FairExplore


