-- Prove2me | Definitions.Def_StructBandit_regret
-- name    : StructBandit_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:58.368117+00:00
-- url     : https://prove2.me/theorems/21129561-17fa-4103-a4f1-c95092965fff
-- title:
--   Histories, policies, the stochastic environment and the regret $\mathrm{Reg}_\pi(T,P)$
-- statement:
--   A **history** is the sequence $(x_1,R_1(x_1),\dots,x_{t-1},R_{t-1}(x_{t-1}))$ of arms played and rewards observed before round $t$; $N_t(x)$ counts the pulls of $x$ and $P_t$ is the empirical reward distribution. A **policy** chooses the arm of round $t$ as a function of an independent randomization seed and the history. The environment is a probability space carrying rewards $R_t(x)$, independent across all arms and rounds with law $P(\cdot,x)$, and a seed independent of them. The **regret** of a policy $\pi$ is
--
--   $$
--   \mathrm{Reg}_\pi(T,P):=T\max_{x\in X}\sum_r rP(r,x)-\sum_{t=1}^T\mathbb E\Big[\sum_r rP(r,x^\pi_t)\Big].
--   $$
--
--   **Formalization Note** Histories are lists, newest first. `IsAdmissible π` makes the arm measurable in the seed (the class $\Pi$ of p.7). `histSigma n` is $\sigma(\text{seed},x_1,R_1(x_1),\dots,x_n,R_n(x_n))$.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, §3, p.7, Eq. (2)

import Mathlib
import Definitions.Def_StructBandit_IsStructureSet

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StructBandit

/-- A **history** `h_t = (x_1, R_1(x_1), …, x_{t−1}, R_{t−1}(x_{t−1}))` (arXiv:2007.07302v3, p.7),
stored newest first: the head of the list is the last round played. A history of length `n` is the
information available in round `t = n + 1`. -/
abbrev History (R : Finset ℝ) (X : Type*) : Type _ := List (X × R)

open Classical in
/-- `N_t(x)`: the number of rounds of the history in which arm `x` was pulled. -/
noncomputable def pullCount {R : Finset ℝ} {X : Type*} (h : History R X) (x : X) : ℕ :=
  h.countP (fun p => decide (p.1 = x))

open Classical in
/-- `P_t`: the empirical reward distribution of the history, `P_t(r,x) = #{rounds with x pulled and
reward r} / N_t(x)`.

**Formalization Note.** Algorithm 1 (p.24) builds `P_t` by a point mass after the initial pulls and the
recursive update of "Updating variables"; that recursion produces exactly this empirical distribution.
It is used only where `N_t(x) ≥ 1`, or multiplied by `N_t(x)`. -/
noncomputable def empDist {R : Finset ℝ} {X : Type*} (h : History R X) : R → X → ℝ :=
  fun r x => (h.countP (fun p => decide (p = (x, r))) : ℝ) / (pullCount h x : ℝ)

open Classical in
/-- The argmin set `argmin_{x ∈ A} f(x)` (all minimizers, ties kept). -/
noncomputable def argminOn {X α : Type*} [LinearOrder α] (A : Finset X) (f : X → α) : Finset X :=
  A.filter (fun x => ∀ y ∈ A, f x ≤ f y)

/-- A (possibly randomized) **non-anticipating policy**: the arm of round `t` is a function of an
independent randomization seed `v` and of the history `h_t` of the previous rounds. -/
abbrev Policy (V : Type*) (R : Finset ℝ) (X : Type*) : Type _ := V → History R X → X

/-- A policy is in `Π` (p.7): its arm selection is measurable in the seed for every history, so that the
arm `x_t` is `F_t`-measurable with `F_t = σ(seed, x_1, R_1(x_1), …, x_{t−1}, R_{t−1}(x_{t−1}))`. -/
def IsAdmissible {V : Type*} [MeasurableSpace V] {R : Finset ℝ} {X : Type*} (π : Policy V R X) :
    Prop :=
  ∀ (h : History R X) (x : X), MeasurableSet {v | π v h = x}

/-- **The stochastic environment of a structured bandit** (arXiv:2007.07302v3, §3, p.7): on a
probability space `(Ω, μ)`, a reward table `R_t(x) = rew t x` (rounds `t ≥ 1`; index `0` is never
read) whose entries are independent across all arms and rounds and have law `P(·,x)`, and a
randomization seed independent of the table, used by randomized policies (Theorem 3's expectation is
"with respect to the randomness in the observed rewards and choices made by DUSA", p.28).

**Formalization Note.** `μ.real {R_t(x) = r} = P(r,x)`. The seed takes values in an arbitrary
measurable space `V`. -/
structure BanditEnv {R : Finset ℝ} {X : Type*} (P : R → X → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Type*) [MeasurableSpace V] where
  /-- The reward table `R_t(x)`. -/
  rew : ℕ → X → Ω → R
  /-- The randomization seed. -/
  seed : Ω → V
  measurable_rew : ∀ t x, Measurable (rew t x)
  measurable_seed : Measurable seed
  /-- The rewards are independent across all arms and rounds. -/
  indep_rew : iIndepFun (fun p : ℕ × X => rew p.1 p.2) μ
  /-- The seed is independent of the reward table. -/
  indep_seed : IndepFun seed (fun ω (p : ℕ × X) => rew p.1 p.2 ω) μ
  /-- `R_t(x)` has law `P(·,x)`. -/
  law : ∀ t x (r : R), μ.real {ω | rew t x ω = r} = P r x

/-- The history after `n` rounds of policy `π` in the environment `E` (newest first). -/
noncomputable def histAt {R : Finset ℝ} {X : Type*} {P : R → X → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {V : Type*} [MeasurableSpace V] (π : Policy V R X) (E : BanditEnv P μ V) :
    ℕ → Ω → History R X
  | 0 => fun _ => []
  | n + 1 => fun ω =>
      (π (E.seed ω) (histAt π E n ω), E.rew (n + 1) (π (E.seed ω) (histAt π E n ω)) ω)
        :: histAt π E n ω

/-- The arm `x_{n+1}` pulled in round `n + 1`. -/
noncomputable def armAt {R : Finset ℝ} {X : Type*} {P : R → X → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {V : Type*} [MeasurableSpace V] (π : Policy V R X) (E : BanditEnv P μ V)
    (n : ℕ) (ω : Ω) : X :=
  π (E.seed ω) (histAt π E n ω)

/-- The σ-algebra `σ(seed, x_1, R_1(x_1), …, x_n, R_n(x_n))` of the seed and the first `n` rounds
(the paper's `F_{n+1}`, p.7; arms carry the discrete σ-algebra). -/
@[instance_reducible]
noncomputable def histSigma {R : Finset ℝ} {X : Type*} {P : R → X → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {V : Type*} [MeasurableSpace V] (π : Policy V R X) (E : BanditEnv P μ V)
    (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap E.seed inferInstance ⊔
    ⨆ m ∈ Finset.range n,
      (MeasurableSpace.comap (armAt π E m) ⊤ ⊔
        MeasurableSpace.comap (fun ω => E.rew (m + 1) (armAt π E m ω) ω) inferInstance)

/-- **The regret** (arXiv:2007.07302v3, Eq. (2), p.7):
`Reg_π(T,P) := T max_{x∈X} ∑_{r∈R} r P(r,x) − ∑_{t=1}^T E[∑_{r∈R} r P(r, x_t^π)]`. -/
noncomputable def regret {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] {P : R → X → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Type*} [MeasurableSpace V]
    (π : Policy V R X) (E : BanditEnv P μ V) (T : ℕ) : ℝ :=
  T * rewStar P - ∑ n ∈ Finset.range T, ∫ ω, mean P (armAt π E n ω) ∂μ

end StructBandit


