-- Prove2me | Definitions.Def_AllocationIndices_Superprocess
-- name    : AllocationIndices_Superprocess
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T02:47:50.758632+00:00
-- url     : https://prove2.me/theorems/27016ee4-8805-4957-90b1-cc02338deec5
-- title:
--   Chapter 4: decision processes and superprocesses, the superprocess index (4.1), simple families of alternative superprocesses, Condition D, stoppable bandits, index functions and ε-index policies
-- statement:
--   The objects of Chapter 4, in discrete time on countable state spaces with bounded rewards.
--
--   **Decision processes and superprocesses (§4.2).** A `DecisionProcess S U` has, in each state $x$, a nonempty finite control set $\Gamma(x) \subseteq U$; applying $u$ yields the reward $r(x, u)$ and moves the state by the Markov kernel $P(\cdot \mid x, u)$. Adding the freeze control (state unchanged, no reward) turns it into a **superprocess**. A deterministic stationary Markov policy $g : S \to U$ is feasible if $g(x) \in \Gamma(x)$; operating $D$ under $g$ gives the **bandit process** $D_g$ with kernel $x \mapsto P(\cdot \mid x, g(x))$ (`stationaryKernel`) and reward $x \mapsto r(x, g(x))$ (`stationaryReward`). The **superprocess index** (4.1) is
--   $$\nu(S, x, u) = \sup_{g\ \text{feasible},\ g(x) = u} \nu(D_g, x) \quad (\texttt{superIndex}), \qquad \nu(S, x) = \max_{u \in \Gamma(x)} \nu(S, x, u) \quad (\texttt{superIndexMax}),$$
--   with $\nu(D_g, x)$ the Gittins index of the *Bandit Algorithms* model; the supremum is a real supremum over the nonempty (for $u \in \Gamma(x)$) family of feasible $g$ with $g(x) = u$, bounded by the reward bound.
--
--   **A simple family of alternative superprocesses (SFAS).** $n$ superprocesses on a common $(S, U)$ (distinct superprocesses are the disjoint-union case, as in the Bandit Algorithms model). A history of $t$ decision times records the state-vector observed and the pair (superprocess continued, control applied) at each, plus the current state-vector (`SFASHistory`); a **policy** is a Markov kernel per decision time from the history to that pair (`SFASPolicy`), **feasible** if the control is almost surely in the control set of the superprocess continued (`IsFeasiblePolicy`). The run law `sfasMeasure D π x t` is built decision time by decision time exactly as `markovBanditMeasure`: the pair is drawn from the policy, the continued superprocess moves by $P(\cdot \mid x_i, u)$, the others are frozen. The **payoff** `sfasValue D a π x` is $\sum_t a^t\,\mathbb{E}[r(x_{i_t}(t), u_t)]$. A policy is **optimal** (`IsOptimalSFASPolicy`) if it is feasible and attains the supremum of the payoff over feasible policies from every initial state-vector (p. 22). The **index policy** of Theorem 4.3 with a control function $g$ (`IsSuperIndexPolicy D a g`) almost surely continues, at every decision time, a superprocess $i$ of maximal index $\nu(S, x_i) = \max_{u \in \Gamma(x_i)} \nu(S, x_i, u)$ and applies the control $g(x_i)$. When $g$ is a Condition-D control, $\nu(S, x, g(x)) = \nu(S, x)$, so this is an index policy in the book's sense; the control is pinned to $g$ because an index policy that breaks a tie among controls against $g$ need not be optimal (a control paying $1$ and then $0$ forever ties in index with one paying $1$ forever).
--
--   **Condition D (p. 83).** `withStandard D lam` is the SFAS $\{S, \Lambda\}$ of $S$ and a standard bandit process $\Lambda$ with parameter $\lambda$ (one state, every control available, reward $\lambda$, state unchanged) on $S \oplus \mathrm{Unit}$. "It is optimal to select $S$ in state $x$" (`OptimalToSelect`) means some optimal policy for $\{S, \Lambda\}$ continues $S$ at time $0$ from $(x, \Lambda)$; "it is optimal to apply $u$ to $S$" (`OptimalToApply`) that some optimal policy continues $S$ with control $u$ at time $0$. **Condition D** (`ConditionD D a`, with `IsConditionDControl D a g` for the function itself): there is a feasible $g$ such that for all $x$ and $\lambda$ for which it is optimal to select $S$ in state $x$, it is optimal to apply $g(x)$.
--
--   **Stoppable bandit processes (§4.4).** `stoppable P r μ` is the bandit process $(P, r)$ with a stop control under which the state is unchanged and the reward is $\mu(x)$, so that the process then behaves as a standard bandit process with parameter $\mu(x)$; `HasImprovingStoppingOption P μ` says $\mu(x(t))$ is almost surely nondecreasing in process time from every initial state.
--
--   **Index functions (Theorem 4.8).** An `IndexFunction` assigns a real number to every bandit process (kernel and reward on any measurable state space) and state. `IsIndexForStandardPairs μ a`: for every bandit process $B = (P, r)$ on a countable state space with bounded reward and every standard bandit $\Lambda(\lambda)$, every policy for the SFABP $\{B, \Lambda\}$ (the two-armed Bandit Algorithms model on $T \oplus \mathrm{Unit}$) that continues an arm of maximal $\mu$-value at each decision time attains the supremum of the discounted value from $(x, \Lambda)$, for every $x$.
--
--   **$\varepsilon$-index policies (§4.10).** `IsEpsIndexPolicy P r a ε π`: at every decision time the Gittins index of the bandit continued is almost surely within $\varepsilon$ of the maximal index among the current states.
--
--   **Conventions.** Decision times are $0, 1, 2, \dots$; all expectations are Bochner integrals of bounded measurable functions under finite-horizon laws; the discounted series converge absolutely for bounded rewards and $a < 1$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, Chapter 4: §4.2 superprocesses and the index (4.1) (pp. 80-82), Condition D and Note 4.2 (p. 83), §4.3 index policies for a SFAS (p. 83), §4.4 stoppable bandit processes (p. 88), Theorem 4.8's 'index for B_a' (p. 96), §4.10 ε-index policies (p. 112)

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_AllocationIndices_Jobs

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
Chapter 4 (pp. 79-113): superprocesses, precedence constraints and arrivals.

**Superprocesses (§4.2).** A decision process `D` on a countable state space `S` with a finite
control type `U`: in state `x` a control `u ∈ Γ(x)` (a nonempty finite set) yields the reward
`r(x, u)` and moves the state by the kernel `P(· | x, u)`. Adding the freeze control (state
unchanged, no reward) makes it a **superprocess** `S`; a simple family of alternative
superprocesses (SFAS) is `n` such superprocesses on a common `(S, U)` (different superprocesses
are the disjoint-union special case, as in the Bandit Algorithms model), of which exactly one is
continued, with a control from its control set, at each decision time. Time is discrete,
`0, 1, 2, …`, and rewards are discounted by `a^t`.

* `DecisionProcess S U`, `stationaryKernel D g`, `stationaryReward D g` — the bandit process
  `D_g` obtained by operating `D` under a deterministic stationary Markov policy `g : S → U`.
* `superIndex D a x u = ν(S, x, u) = sup_{g : g(x) = u} ν(D_g, x)` (4.1), `superIndexMax D a x =
  ν(S, x) = max_{u ∈ Γ(x)} ν(S, x, u)`.
* `SFASHistory n S U t`, `SFASPolicy n S U`, `IsFeasiblePolicy`, `sfasStepKernel`,
  `sfasMeasure`, `sfasRoundReward`, `sfasValue` — the `n`-superprocess family: a policy is a
  Markov kernel per round from the history to the pair (superprocess, control), the run law is
  built as in `markovBanditMeasure`, and the payoff is the discounted series of expected
  per-round rewards. `IsOptimalSFASPolicy` — a feasible policy attaining the supremum of the
  payoff from every initial state-vector. `IsSuperIndexPolicy` — an index policy with respect to
  `ν(·, ·, ·)`.
* `withStandard D lam` — the superprocess `S` together with a standard bandit process `Λ` with
  parameter `lam` (one state, reward `lam`), on `S ⊕ Unit`; `OptimalToSelect`, `OptimalToApply`
  — "it is optimal to select `S` in state `x`", resp. "to apply the control `u` to it", in the
  SFAS `{S, Λ}`: some optimal policy does so at time `0` from the initial state `(x, Λ)`;
  `ConditionD D a` — Whittle's Condition D (p. 83).
* `stoppable P r μ` — a stoppable bandit process (§4.4): the bandit process `(P, r)` with a stop
  control that makes it behave as a standard bandit process with parameter `μ(x)`;
  `HasImprovingStoppingOption` — `μ(x(t))` almost surely nondecreasing in process time.
* `IndexFunction` — a real-valued function of a bandit process and its state, defined for every
  bandit process (any measurable state space); `standardKernel` — the one-state kernel;
  `IsIndexForStandardPairs μ a` — `μ` defines optimal index policies for every SFABP
  `{B, Λ}` of a bandit process and a standard bandit (Theorem 4.8's hypothesis in the form its
  proof uses).
* `IsEpsIndexPolicy P r a ε π` — an `ε`-index policy for a SFABP of the Bandit Algorithms model:
  the index of the bandit continued at each decision time is within `ε` of the maximal index
  (Theorem 4.18, p. 112).
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

noncomputable section

namespace AllocationIndices

/-! ### Decision processes and superprocesses -/

/-- A discrete-time decision process on the state space `S` with controls of type `U` (p. 80): in
state `x` the available controls form the nonempty finite set `avail x`; applying `u` yields
`reward x u` and moves the state according to `step u x`. -/
structure DecisionProcess (S U : Type*) [MeasurableSpace S] where
  /-- The transition kernel under control `u`. -/
  step : U → Kernel S S
  /-- The reward for applying control `u` in state `x`. -/
  reward : S → U → ℝ
  /-- The control set `Γ(x)`. -/
  avail : S → Finset U
  avail_nonempty : ∀ x, (avail x).Nonempty
  markov : ∀ u, IsMarkovKernel (step u)

attribute [instance] DecisionProcess.markov

variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The rewards of a decision process are bounded (the standing assumption of §2.4 for the
constituent bandit processes). -/
def DecisionProcess.BoundedRewards (D : DecisionProcess S U) : Prop :=
  ∃ M : ℝ, ∀ x u, |D.reward x u| ≤ M

/-- A deterministic stationary Markov policy `g` for `D` is feasible if `g(x) ∈ Γ(x)`. -/
def DecisionProcess.IsFeasibleStationary (D : DecisionProcess S U) (g : S → U) : Prop :=
  ∀ x, g x ∈ D.avail x

/-- The transition kernel of the bandit process `D_g`: `D` operated under the stationary policy
`g`. -/
def stationaryKernel (D : DecisionProcess S U) (g : S → U) : Kernel S S where
  toFun x := D.step (g x) x
  measurable' := measurable_of_countable _

instance stationaryKernel.instIsMarkovKernel (D : DecisionProcess S U) (g : S → U) :
    IsMarkovKernel (stationaryKernel D g) :=
  ⟨fun x ↦ (D.markov (g x)).isProbabilityMeasure x⟩

/-- The reward function of the bandit process `D_g`. -/
def stationaryReward (D : DecisionProcess S U) (g : S → U) : S → ℝ :=
  fun x ↦ D.reward x (g x)

/-- The superprocess index (4.1): `ν(S, x, u) = sup_{g : g(x) = u} ν(D_g, x)`, the supremum over
feasible deterministic stationary Markov policies `g` applying `u` at `x` of the Gittins index of
the bandit process `D_g` at `x`. -/
def superIndex (D : DecisionProcess S U) (a : ℝ) (x : S) (u : U) : ℝ :=
  ⨆ g : {g : S → U // D.IsFeasibleStationary g ∧ g x = u},
    gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x

/-- `ν(S, x) = max_{u ∈ Γ(x)} ν(S, x, u)`. -/
def superIndexMax (D : DecisionProcess S U) (a : ℝ) (x : S) : ℝ :=
  (D.avail x).sup' (D.avail_nonempty x) (superIndex D a x)

/-! ### A simple family of alternative superprocesses -/

/-- The history of `t` completed decision times of a family of `n` superprocesses together with
the current state-vector: for each past decision time the state-vector observed and the pair
(superprocess continued, control applied). -/
abbrev SFASHistory (n : ℕ) (S U : Type*) (t : ℕ) :=
  (Fin t → (Fin n → S) × (Fin n × U)) × (Fin n → S)

/-- A policy for a family of `n` superprocesses: for each decision time, a Markov kernel from the
history to the pair (superprocess to continue, control to apply). -/
structure SFASPolicy (n : ℕ) (S U : Type*) [MeasurableSpace S] [MeasurableSpace U] where
  /-- The conditional law of the choice at decision time `t` given the history. -/
  select : (t : ℕ) → Kernel (SFASHistory n S U t) (Fin n × U)
  markov : ∀ t, IsMarkovKernel (select t)

attribute [instance] SFASPolicy.markov

variable [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] {n : ℕ}

/-- A policy is feasible if the control it applies is almost surely in the control set of the
superprocess it continues. -/
def IsFeasiblePolicy (D : DecisionProcess S U) (π : SFASPolicy n S U) : Prop :=
  ∀ t (h : SFASHistory n S U t), (π.select t) h {c | c.2 ∈ D.avail (h.2 c.1)} = 1

/-- One decision time: given the history, sample the pair `(i, u)` from the policy and the next
state of superprocess `i` from `D.step u`; the pair and the new state are returned. -/
def sfasStepKernel (D : DecisionProcess S U) (π : SFASPolicy n S U) (t : ℕ) :
    Kernel (SFASHistory n S U t) ((Fin n × U) × S) :=
  (π.select t).compProd
    (Kernel.mk (fun p : SFASHistory n S U t × (Fin n × U) ↦ D.step p.2.2 (p.1.2 p.2.1))
      (by
        refine measurable_from_prod_countable_left fun c ↦ ?_
        exact (D.step c.2).measurable.comp ((measurable_pi_apply c.1).comp measurable_snd)))

instance sfasStepKernel.instIsMarkovKernel (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (t : ℕ) : IsMarkovKernel (sfasStepKernel D π t) := by
  rw [sfasStepKernel]
  have : IsMarkovKernel (Kernel.mk (fun p : SFASHistory n S U t × (Fin n × U) ↦
      D.step p.2.2 (p.1.2 p.2.1)) (by
        refine measurable_from_prod_countable_left fun c ↦ ?_
        exact (D.step c.2).measurable.comp ((measurable_pi_apply c.1).comp measurable_snd))) :=
    ⟨fun p ↦ (D.markov p.2.2).isProbabilityMeasure _⟩
  infer_instance

/-- Appending a decision time to the history and updating the continued superprocess's state. -/
lemma measurable_sfasSnoc {t : ℕ} :
    Measurable (fun p : SFASHistory n S U t × ((Fin n × U) × S) ↦
      ((Fin.snoc (α := fun _ ↦ (Fin n → S) × (Fin n × U)) p.1.1 (p.1.2, p.2.1),
        Function.update p.1.2 p.2.1.1 p.2.2) : SFASHistory n S U (t + 1))) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_finSnoc.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))
  · exact measurable_updateArmState.comp
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)))

/-- The law of the history of the first `t` decision times of the family under policy `π`,
started from the state-vector `x`. -/
def sfasMeasure (D : DecisionProcess S U) (π : SFASPolicy n S U) (x : Fin n → S) :
    (t : ℕ) → Measure (SFASHistory n S U t)
  | 0 => Measure.dirac (fun i ↦ i.elim0, x)
  | t + 1 =>
      ((sfasMeasure D π x t).compProd (sfasStepKernel D π t)).map
        (fun p ↦ (Fin.snoc (α := fun _ ↦ (Fin n → S) × (Fin n × U)) p.1.1 (p.1.2, p.2.1),
          Function.update p.1.2 p.2.1.1 p.2.2))

instance sfasMeasure.instIsProbabilityMeasure (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (x : Fin n → S) (t : ℕ) : IsProbabilityMeasure (sfasMeasure D π x t) := by
  induction t with
  | zero => rw [sfasMeasure]; exact Measure.dirac.isProbabilityMeasure
  | succ t ih =>
      rw [sfasMeasure]
      have := ih
      exact Measure.isProbabilityMeasure_map measurable_sfasSnoc.aemeasurable

/-- The expected reward collected at decision time `t` (0-indexed): the reward of the control
applied to the superprocess continued, in its state at that time. -/
def sfasRoundReward (D : DecisionProcess S U) (π : SFASPolicy n S U) (x : Fin n → S) (t : ℕ) :
    ℝ :=
  ∫ h, D.reward ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2.1)) ((h.1 (Fin.last t)).2.2)
    ∂sfasMeasure D π x (t + 1)

/-- The payoff of the family under policy `π` from the state-vector `x`: the expected total
discounted reward `∑_t a^t E[reward at t]`. -/
def sfasValue (D : DecisionProcess S U) (a : ℝ) (π : SFASPolicy n S U) (x : Fin n → S) : ℝ :=
  ∑' t : ℕ, a ^ t * sfasRoundReward D π x t

/-- An optimal policy (p. 22): feasible, and maximizing the payoff over all feasible policies for
every initial state-vector. -/
def IsOptimalSFASPolicy (D : DecisionProcess S U) (a : ℝ) (π : SFASPolicy n S U) : Prop :=
  IsFeasiblePolicy D π ∧ ∀ x : Fin n → S,
    sfasValue D a π x = ⨆ π' : {π' : SFASPolicy n S U // IsFeasiblePolicy D π'}, sfasValue D a π' x

/-- The index policy of Theorem 4.3 with respect to `ν(S_1, ·, ·), …, ν(S_n, ·, ·)` (§4.3) that
applies the control `g`: at every decision time the superprocess continued, `i`, almost surely has
maximal index `ν(S, x_i) = max_{u ∈ Γ(x_i)} ν(S, x_i, u)` among all superprocesses, and the control
applied is `g(x_i)`. For a Condition-D control `g` (`IsConditionDControl`) one has
`ν(S, x, g(x)) = ν(S, x)`, so this is an index policy in the book's sense, with the ties among
controls broken as the book's proof breaks them. That choice matters: a control paying `1` and
then `0` forever has the same index as one paying `1` forever, and an index policy that picks the
first is not optimal. -/
def IsSuperIndexPolicy (D : DecisionProcess S U) (a : ℝ) (g : S → U) (π : SFASPolicy n S U) :
    Prop :=
  ∀ t (h : SFASHistory n S U t),
    (π.select t) h {c | c.2 = g (h.2 c.1) ∧
      ∀ j, superIndexMax D a (h.2 j) ≤ superIndexMax D a (h.2 c.1)} = 1

/-! ### Condition D -/

/-- The superprocess `S` together with a standard bandit process `Λ` with parameter `lam`: on
`S ⊕ Unit`, the extra state has every control available, keeps its state and pays `lam`. -/
def withStandard [Fintype U] [Nonempty U] (D : DecisionProcess S U) (lam : ℝ) :
    DecisionProcess (S ⊕ Unit) U where
  step u := sumKernel (D.step u) (Kernel.const Unit (Measure.dirac ()))
  reward := Sum.elim (D.reward) (fun _ _ ↦ lam)
  avail := Sum.elim D.avail (fun _ ↦ univ)
  avail_nonempty := by
    rintro (x | u)
    · exact D.avail_nonempty x
    · exact univ_nonempty
  markov u := inferInstance

/-- The initial history of the family `{S, Λ}` with `S` in state `x`. -/
def standardStart (x : S) : SFASHistory 2 (S ⊕ Unit) U 0 :=
  (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])

/-- "It is optimal to select `S` when it is in state `x`" in the SFAS `{S, Λ}` with parameter
`lam`: some optimal policy continues `S` (with some control) at time `0` from `(x, Λ)`. -/
def OptimalToSelect [Fintype U] [Nonempty U] (D : DecisionProcess S U) (a : ℝ) (lam : ℝ) (x : S) : Prop :=
  ∃ π : SFASPolicy 2 (S ⊕ Unit) U, IsOptimalSFASPolicy (withStandard D lam) a π ∧
    (π.select 0) (standardStart x) {c | c.1 = 0} = 1

/-- "It is optimal to apply the control `u` to `S` in state `x`" in the SFAS `{S, Λ}`: some
optimal policy continues `S` with control `u` at time `0` from `(x, Λ)`. -/
def OptimalToApply [Fintype U] [Nonempty U] (D : DecisionProcess S U) (a : ℝ) (lam : ℝ) (x : S) (u : U) :
    Prop :=
  ∃ π : SFASPolicy 2 (S ⊕ Unit) U, IsOptimalSFASPolicy (withStandard D lam) a π ∧
    (π.select 0) (standardStart x) {(0, u)} = 1

/-- `g` is a Condition-D control for `S` (p. 83): `g` is feasible and, for all `x` and `lam` for
which it is optimal to select `S` in state `x` in the SFAS `{S, Λ(lam)}`, it is optimal to apply
the control `g(x)`. -/
def IsConditionDControl [Fintype U] [Nonempty U] (D : DecisionProcess S U) (a : ℝ) (g : S → U) :
    Prop :=
  D.IsFeasibleStationary g ∧ ∀ x lam, OptimalToSelect D a lam x → OptimalToApply D a lam x (g x)

/-- Whittle's Condition D (p. 83): there is a feasible function `g` such that, for all `x` and
`lam` for which it is optimal to select `S` in state `x` in the SFAS `{S, Λ(lam)}`, it is optimal
to apply the control `g(x)` (the optimal control does not depend on `lam`). -/
def ConditionD [Fintype U] [Nonempty U] (D : DecisionProcess S U) (a : ℝ) : Prop :=
  ∃ g : S → U, IsConditionDControl D a g

/-! ### Stoppable bandit processes -/

/-- A stoppable bandit process (§4.4): the bandit process `(P, r)` with a stop control (`false`)
under which the state is unchanged and the reward is `μ(x)`, i.e. the process behaves as a
standard bandit process with parameter `μ(x)`; `true` is the continuation control. -/
def stoppable (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ) : DecisionProcess S Bool where
  step u := if u then P else Kernel.id
  reward x u := if u then r x else μ x
  avail _ := univ
  avail_nonempty _ := univ_nonempty
  markov u := by cases u <;> simp <;> infer_instance

/-- The stopping option improves: `μ(x(t))` is almost surely nondecreasing in process time, for
every initial state. -/
def HasImprovingStoppingOption (P : Kernel S S) [IsMarkovKernel P] (μ : S → ℝ) : Prop :=
  ∀ x, markovChainMeasure P x {ω | ∀ t, μ (ω t) ≤ μ (ω (t + 1))} = 1

/-! ### Indices for the class of all bandit processes (Theorem 4.8) -/

/-- A candidate index: a real-valued function of a bandit process (kernel and reward on any
measurable state space) and its state. -/
def IndexFunction : Type 1 :=
  ∀ (T : Type) [MeasurableSpace T], Kernel T T → (T → ℝ) → T → ℝ

/-- The kernel of a standard bandit process: one state, which never changes. -/
def standardKernel : Kernel Unit Unit :=
  Kernel.const Unit (Measure.dirac ())

instance standardKernel.instIsMarkovKernel : IsMarkovKernel standardKernel := by
  unfold standardKernel
  infer_instance

/-- The value of the candidate index `μ` on the two arms of the family `{B, Λ(lam)}` with
`B = (P, r)` on `T`, as a function of the arm's state in `T ⊕ Unit`. -/
def sumIndexValue (μ : IndexFunction) {T : Type} [MeasurableSpace T] (P : Kernel T T)
    (r : T → ℝ) (lam : ℝ) : T ⊕ Unit → ℝ :=
  Sum.elim (μ T P r) (fun _ ↦ μ Unit standardKernel (fun _ ↦ lam) ())

/-- `μ` is an index for every SFABP `{B, Λ}` formed from a bandit process on a countable state
space with bounded reward and a standard bandit process: every policy that continues an arm of
maximal `μ`-value at each decision time attains the supremum of the discounted value from every
initial pair of states. -/
def IsIndexForStandardPairs (μ : IndexFunction) (a : ℝ) : Prop :=
  ∀ (T : Type) [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]
    (P : Kernel T T) [IsMarkovKernel P] (r : T → ℝ), BoundedReward r → ∀ (lam : ℝ)
    (π : MarkovBanditPolicy 2 (T ⊕ Unit)),
    (∀ t (h : MarkovBanditHistory 2 (T ⊕ Unit) t),
      (π.select t) h {i | ∀ j, sumIndexValue μ P r lam (h.2 j) ≤ sumIndexValue μ P r lam (h.2 i)} = 1) →
    ∀ x : T, markovBanditDiscountedValue (sumKernel P standardKernel)
        (sumReward r (fun _ ↦ lam)) a π (twoStates x ()) =
      ⨆ π' : MarkovBanditPolicy 2 (T ⊕ Unit), markovBanditDiscountedValue
        (sumKernel P standardKernel) (sumReward r (fun _ ↦ lam)) a π' (twoStates x ())

/-! ### ε-index policies (§4.10) -/

/-- An `ε`-index policy for a SFABP of the Bandit Algorithms model (p. 112): the Gittins index
of the bandit continued at each decision time is almost surely within `ε` of the maximal index at
that time. -/
def IsEpsIndexPolicy {T : Type*} [MeasurableSpace T] {k : ℕ} (P : Kernel T T) [IsMarkovKernel P]
    (r : T → ℝ) (a ε : ℝ) (π : MarkovBanditPolicy k T) : Prop :=
  ∀ t (h : MarkovBanditHistory k T t),
    (π.select t) h {i | ∀ j, gittinsIndex P r a (h.2 j) - ε ≤ gittinsIndex P r a (h.2 i)} = 1

end AllocationIndices

end


