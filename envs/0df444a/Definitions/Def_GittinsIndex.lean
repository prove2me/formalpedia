-- Prove2me | Definitions.Def_GittinsIndex
-- name    : GittinsIndex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-30T15:43:06.952048+00:00
-- url     : https://prove2.me/theorems/a0b22bb0-7ffc-4338-84ae-860bfd3dbced
-- statement:
--   The discounted $k$-armed Markov bandit (L&S §35.4): each arm is a Markov chain on a measurable state space $S$ with common transition kernel $P$, reward $r : S \to \mathbb{R}$ and discount $\alpha \in (0,1)$. `markovChainMeasure P x` is the Ionescu–Tulcea law $\mathbb{P}_x$ of the single-arm chain started at $x$; stopping times are $\overline{\mathbb{N}}$-valued maps adapted to the coordinate filtration. The Gittins index (Eq. 35.9, 0-indexed) is
--
--   $$g(x) = \sup_{\tau \ge 1} \frac{\mathbb{E}_x\!\left[\sum_{t<\tau} \alpha^t r(S_t)\right]}{\mathbb{E}_x\!\left[\sum_{t<\tau} \alpha^t\right]}.$$
--
--   A `MarkovBanditPolicy` is a family of Markov kernels from the game history $(S^k \times [k])^t \times S^k$ to arms (§35.4.2); `markovBanditMeasure` is the finite-horizon law of the game in which only the activated chain moves. The $\alpha$-discounted value of a policy is the series of per-round expected rewards over the finite-horizon marginals,
--
--   $$\sum_t \alpha^t\, \mathbb{E}\big[r(S_{A_{t+1}}(t+1))\big].$$
--
--   Assumption 35.6 (`DiscountedRewardIntegrable`) is
--
--   $$\mathbb{E}_x\Big[\sum_t \alpha^{t-1}|r(S_t)|\Big] < \infty \quad\text{for every } x.$$
--
--   A Gittins index policy (`IsGittinsIndexPolicy`) activates, a.s. in every round, an arm whose current state has maximal index (ties arbitrary).
-- source:
--   L&S Ch 35.2, 35.4, pp.441-450

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §35.4:
the discounted `k`-armed Markov bandit and the Gittins index.

**Single arm.** An arm is a time-homogeneous Markov chain on a measurable state
space `S` with transition kernel `P`, reward function `r : S → ℝ` and discount
factor `α ∈ (0,1)`. `markovChainMeasure P x` is the law `ℙ_x` of the chain
started at `x`, built from the Ionescu–Tulcea kernel `Kernel.trajMeasure`
(we index time from `0`, so the book's `S_t`, `t = 1, 2, …` is our `ω (t-1)`).
Stopping times of the chain are `ℕ∞`-valued maps adapted to the natural
coordinate filtration. The **Gittins index** (fair charge) of a state `x` is
(L&S Eq. (35.9), 0-indexed; the book's `τ ≥ 2` becomes `1 ≤ τ`)

  `g(x) = sup_{τ ≥ 1} E_x[∑_{t<τ} α^t r(S_t)] / E_x[∑_{t<τ} α^t]`,

equivalently the retirement-value characterization `g(x) = inf {γ : v_γ(x) = 0}`
of Eq. (35.8).

**The `k`-armed game** (§35.4.2). `k` chains share the state space `S` and the
kernel `P` (non-restrictive: take disjoint unions). Each round the learner sees
all current states, activates one arm `A_t`, receives `r(S_{A_t}(t))`, and only
the activated chain moves. A policy is a family of Markov kernels from the
history `(S^k × [k])^t × S^k` (past state-vectors and actions, plus the current
state-vector) to arms, mirroring `BanditPolicy`. `markovBanditMeasure P π x t`
is the finite-horizon law of the first `t` rounds; the α-discounted value of a
policy is the discounted series of per-round expected rewards
`∑' t, α^t * E[r(S_{A_{t+1}}(t+1))]`, which avoids any infinite-horizon measure
on the game (each summand only uses the horizon-`(t+1)` marginal; under the
integrability Assumption 35.6 this agrees with the book's
`E[∑_{t=1}^∞ α^{t-1} r(S_{A_t}(t))]` by Fubini). A **Gittins index policy**
activates an arm whose current state has maximal index (ties arbitrary).
-/

open MeasureTheory ProbabilityTheory

/-! ### The single-arm Markov reward process and the Gittins index -/

namespace BanditAlgorithm

section SingleArm

variable {S : Type*} [MeasurableSpace S]

/-- The one-step kernels of the time-homogeneous Markov chain with transition
kernel `P`, in the form consumed by the Ionescu–Tulcea construction: the state
at time `n + 1` is drawn from `P` applied to the state at time `n`. -/
noncomputable def markovChainStep (P : Kernel S S) (n : ℕ) :
    Kernel (Π _i : Finset.Iic n, S) S :=
  P.comap (fun ω ↦ ω ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance markovChainStep.instIsMarkovKernel (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (markovChainStep P n) := by
  rw [markovChainStep]; infer_instance

/-- `ℙ_x`: the law of the Markov chain `(S_t)_{t=0,1,2,…}` with transition
kernel `P` started at `S_0 = x` (Ionescu–Tulcea; L&S §35.2 and §35.4.1 —
the book indexes time from `1`, we index from `0`). -/
noncomputable def markovChainMeasure (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ ↦ S) (Measure.dirac x) (markovChainStep P)

/-- The natural filtration of the coordinate process on trajectories:
`𝓕 n = σ(S_0, …, S_n)`. -/
@[reducible]
def trajectoryFiltration (S : Type*) [MeasurableSpace S] (n : ℕ) :
    MeasurableSpace (ℕ → S) :=
  MeasurableSpace.comap (fun ω (i : Finset.Iic n) ↦ ω i.1) inferInstance

/-- A stopping time of the coordinate process on `ℕ → S`: an `ℕ∞`-valued map
(`τ = ⊤` = never stop) such that `{τ ≤ n}` is measurable with respect to the
coordinates up to time `n`, for every `n`. -/
def IsTrajStoppingTime {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞) : Prop :=
  ∀ n : ℕ, MeasurableSet[trajectoryFiltration S n] {ω | τ ω ≤ (n : ℕ∞)}

/-- The α-discounted reward accumulated strictly before the stopping time `τ`:
`∑_{t < τ(ω)} α^t · f(ω t)` (the book's `∑_{t=1}^{τ-1} α^{t-1} f(S_t)`,
0-indexed). -/
noncomputable def discountedStoppedSum {S : Type*} (α : ℝ) (f : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) : ℝ :=
  ∑' t : ℕ, if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0

/-- **Assumption 35.6** of L&S: from every initial state, the discounted sum of
absolute rewards of the single-arm chain has finite expectation,
`E_x[∑_{t=1}^∞ α^{t-1} |r(S_t)|] < ∞`. -/
def DiscountedRewardIntegrable (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) : Prop :=
  ∀ x : S,
    ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|) ∂markovChainMeasure P x < ⊤

/-- The **Gittins index** (fair charge) of state `x` (L&S Eq. (35.9), the
stopping-time form of the retirement-value definition Eq. (35.8)): the supremum
over stopping times `τ ≥ 1` (book: `τ ≥ 2`) of

  `E_x[∑_{t<τ} α^t r(S_t)] / E_x[∑_{t<τ} α^t]`.

The denominator is at least `1` since `τ ≥ 1`; under Assumption 35.6
(`DiscountedRewardIntegrable`) every numerator is a genuine (finite) Bochner
integral. -/
noncomputable def gittinsIndex (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (x : S) : ℝ :=
  sSup {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)}

end SingleArm

/-! ### The discounted `k`-armed Markov bandit -/

section MultiArm

variable {S : Type*} [MeasurableSpace S]

/-- A history of `n` completed rounds of the `k`-armed Markov bandit together
with the currently observed states (L&S §35.4.2): for each past round, the
state-vector observed at its start and the arm activated; plus the current
state-vector `(S_1(n+1), …, S_k(n+1))`. -/
abbrev MarkovBanditHistory (k : ℕ) (S : Type*) (n : ℕ) :=
  (Fin n → (Fin k → S) × Fin k) × (Fin k → S)

/-- A policy for the `k`-armed Markov bandit (L&S §35.4.2): for each round, a
Markov kernel from the observed history `(S^k × [k])^n × S^k` to the arm
activated next. -/
structure MarkovBanditPolicy (k : ℕ) (S : Type*) [MeasurableSpace S] where
  /-- The conditional distribution of the arm activated in round `n + 1` given
  the history of the first `n` rounds and the current states. -/
  select : (n : ℕ) → Kernel (MarkovBanditHistory k S n) (Fin k)
  /-- Each round's selection kernel is a Markov kernel. -/
  markov : ∀ n, IsMarkovKernel (select n)

attribute [instance] MarkovBanditPolicy.markov

/-- Evaluating the current state of a chosen arm is jointly measurable. -/
lemma measurable_currentArmState {k n : ℕ} :
    Measurable (fun p : MarkovBanditHistory k S n × Fin k ↦ p.1.2 p.2) :=
  measurable_from_prod_countable_left fun a ↦
    (measurable_pi_apply a).comp measurable_snd

/-- One round of the Markov bandit: given the history, sample the activated arm
`A ~ π.select n` and the next state `Y ~ P(S_A)` of the activated chain,
returning the pair `(A, Y)`. -/
noncomputable def markovBanditStepKernel {k : ℕ} (P : Kernel S S)
    (π : MarkovBanditPolicy k S) (n : ℕ) :
    Kernel (MarkovBanditHistory k S n) (Fin k × S) :=
  (π.select n).compProd (P.comap (fun p ↦ p.1.2 p.2) measurable_currentArmState)

instance markovBanditStepKernel.instIsMarkovKernel {k : ℕ} (P : Kernel S S)
    [IsMarkovKernel P] (π : MarkovBanditPolicy k S) (n : ℕ) :
    IsMarkovKernel (markovBanditStepKernel P π n) := by
  rw [markovBanditStepKernel]; infer_instance

/-- Appending one entry to a finite trajectory is measurable
(generic `Fin.snoc` version of `measurable_banditHistorySnoc`). -/
lemma measurable_finSnoc {E : Type*} [MeasurableSpace E] {n : ℕ} :
    Measurable (fun p : (Fin n → E) × E ↦ Fin.snoc (α := fun _ ↦ E) p.1 p.2) := by
  rw [measurable_pi_iff]
  intro t
  by_cases ht : (t : ℕ) < n
  · have : (fun p : (Fin n → E) × E ↦ Fin.snoc (α := fun _ ↦ E) p.1 p.2 t) =
        fun p ↦ p.1 (Fin.castLT t ht) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst
  · have : (fun p : (Fin n → E) × E ↦ Fin.snoc (α := fun _ ↦ E) p.1 p.2 t) =
        fun p ↦ p.2 := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact measurable_snd

/-- Updating one coordinate of a state-vector at a sampled index is
measurable. -/
lemma measurable_updateArmState {k : ℕ} :
    Measurable (fun p : (Fin k → S) × (Fin k × S) ↦ Function.update p.1 p.2.1 p.2.2) := by
  rw [measurable_pi_iff]
  intro j
  have hset : {p : (Fin k → S) × (Fin k × S) | j = p.2.1} =
      (fun p : (Fin k → S) × (Fin k × S) ↦ p.2.1) ⁻¹' {j} := by
    ext p
    simp [eq_comm]
  have : (fun p : (Fin k → S) × (Fin k × S) ↦ Function.update p.1 p.2.1 p.2.2 j) =
      fun p ↦ if j = p.2.1 then p.2.2 else p.1 j := by
    funext p
    simp [Function.update_apply]
  rw [this]
  refine Measurable.ite ?_ (measurable_snd.comp measurable_snd)
    ((measurable_pi_apply j).comp measurable_fst)
  rw [hset]
  exact (measurable_fst.comp measurable_snd) (measurableSet_singleton j)

/-- The transition applied to a history after one round: record the pair
(current states, activated arm) and move only the activated chain. -/
lemma measurable_markovBanditSnoc {k n : ℕ} :
    Measurable (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦
      ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
        Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1))) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_finSnoc.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))
  · exact measurable_updateArmState.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The finite-horizon law of the `k`-armed Markov bandit (L&S §35.4.2,
Fig. 35.3): starting from the (deterministic) initial state-vector `x`, each
round samples `A_t` from the policy and moves only the activated chain
according to `P`; `markovBanditMeasure P π x n` is the distribution of the
history of the first `n` rounds together with the resulting current states. -/
noncomputable def markovBanditMeasure {k : ℕ} (P : Kernel S S) [IsMarkovKernel P]
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    (n : ℕ) → Measure (MarkovBanditHistory k S n)
  | 0 => Measure.dirac (fun t ↦ t.elim0, x)
  | n + 1 =>
      ((markovBanditMeasure P π x n).compProd (markovBanditStepKernel P π n)).map
        (fun p ↦ (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
          Function.update p.1.2 p.2.1 p.2.2))

instance markovBanditMeasure.instIsProbabilityMeasure {k : ℕ} (P : Kernel S S)
    [IsMarkovKernel P] (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    IsProbabilityMeasure (markovBanditMeasure P π x n) := by
  induction n with
  | zero => rw [markovBanditMeasure]; exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [markovBanditMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map measurable_markovBanditSnoc.aemeasurable

/-- The expected reward collected in round `t` (0-indexed): the reward `r` of
the state of the activated arm, integrated over the horizon-`(t+1)` history
law (the book's `E_π[r(S_{A_{t+1}}(t+1))]`). -/
noncomputable def markovBanditRoundReward {k : ℕ} (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (π : MarkovBanditPolicy k S) (x : Fin k → S) (t : ℕ) : ℝ :=
  ∫ h, r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2))
    ∂markovBanditMeasure P π x (t + 1)

/-- The total expected α-discounted reward of a policy (L&S §35.4.2):
`E_π[∑_{t=1}^∞ α^{t-1} r(S_{A_t}(t))]`, encoded round-by-round as
`∑' t, α^t · E_π[r(S_{A_{t+1}}(t+1))]` over the finite-horizon marginals
(equal to the book's trajectory expectation under Assumption 35.6). -/
noncomputable def markovBanditDiscountedValue {k : ℕ} (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (α : ℝ) (π : MarkovBanditPolicy k S)
    (x : Fin k → S) : ℝ :=
  ∑' t : ℕ, α ^ t * markovBanditRoundReward P r π x t

/-- `IsGittinsIndexPolicy P r α π`: in every round, the activated arm almost
surely maximizes the Gittins index of the current states,
`A_t ∈ argmax_i g(S_i(t))`, with ties broken arbitrarily (L&S §35.4.2). -/
def IsGittinsIndexPolicy {k : ℕ} (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (π : MarkovBanditPolicy k S) : Prop :=
  ∀ n (h : MarkovBanditHistory k S n),
    (π.select n) h
      {a | ∀ j, gittinsIndex P r α (h.2 j) ≤ gittinsIndex P r α (h.2 a)} = 1

end MultiArm

end BanditAlgorithm


