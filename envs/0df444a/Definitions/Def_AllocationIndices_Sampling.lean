-- Prove2me | Definitions.Def_AllocationIndices_Sampling
-- name    : AllocationIndices_Sampling
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:02:10.4579+00:00
-- url     : https://prove2.me/theorems/3569bce6-15c4-4b3e-97cd-624ca8890b8a
-- title:
--   Chapter 7: Bayesian sampling models with conjugate priors, reward and target processes, favourable states, location and scale parameters, and the Bernoulli and normal target processes
-- statement:
--   The objects of Chapter 7, bandit sampling processes.
--
--   **Sampling models (§7.1).** A `SamplingModel Θ P` consists of the likelihood $f(\cdot \mid \theta)$ as a Markov kernel $\Theta \to \mathbb{R}$, a family of priors $\pi(\cdot \mid p)$ on $\Theta$ indexed by the parameters $p \in P$ of a conjugate family (a Markov kernel $P \to \Theta$), and the jointly measurable update $p \mapsto \texttt{update}\ p\ x$ of the parameters after one observation $x$. The **predictive** distribution of the next observation is $f(\cdot \mid p) = \int f(\cdot \mid \theta)\, \pi(d\theta \mid p)$ (`predictive`, the kernel `likelihood ∘ₖ prior`). The family **is conjugate** (`IsConjugate`) if for every $p$ and predictive-almost every $x$ the posterior of $\pi(\cdot \mid p)$ given $X = x$ (Mathlib's `posterior`, the Bayesian inverse of the likelihood kernel) is $\pi(\cdot \mid \texttt{update}\ p\ x)$; this is (7.1)–(7.2) for the parametrized family.
--
--   **Reward and target processes.** The **reward process** has states $p$, moves from $p$ to $\texttt{update}\ p\ x$ with $x$ drawn from the predictive distribution (`rewardChain`), and earns $r(S, \pi) = \int x\, f(x \mid p)\,dx$, the expected next observation (`rewardOf`, (7.3) with $g(x) = x$). The **target process** with target $T$ has states $P \oplus \mathrm{Unit}$, the second summand being the completion state $C$: from $p$ it draws $x$ and moves to $C$ if $x \ge T$, else to $\texttt{update}\ p\ x$ (`targetStep`, `targetChain`; $C$ is absorbing), and earns the **current probability of success** $r(S, \pi) = f([T, \infty) \mid p)$ in $p$ and $0$ in $C$ (`targetReward`). The state $p$ is **favourable** for $T$ (`IsFavourable`, §7.3) if along every finite sequence of observations below $T$ the current probability of success never exceeds its value at $p$.
--
--   **Location and scale parameters (§7.4).** `HasLocationParameter f`: $f(\cdot \mid \mu + c)$ is the image of $f(\cdot \mid \mu)$ under $x \mapsto x + c$; `HasScaleParameter f`: $f(\cdot \mid b\sigma)$ is the image of $f(\cdot \mid \sigma)$ under $x \mapsto bx$ for $b > 0$. For a prior family with parameters $(\bar x, n)$, `PriorHasLocationParameter` (resp. `PriorHasScaleParameter`) says $\bar x$ is a location (resp. scale) parameter of the family in the same sense. `meanUpdate` is the rule $(\bar x, n) \mapsto ((n\bar x + x)/(n+1),\, n+1)$ of Corollaries 7.10 and 7.12.
--
--   **Two target processes.** `bernoulliTargetChain` is the Bernoulli target process of Example 7.5 ($T = 1$, beta prior with parameters $(\alpha, \beta)$): from $(\alpha, \beta)$ the target is reached with the current probability of success $\alpha/(\alpha + \beta)$ (a uniform seed $u < \alpha/(\alpha+\beta)$), otherwise the state moves to $(\alpha, \beta + 1)$; `bernoulliTargetReward` is $\alpha/(\alpha+\beta)$, $0$ in $C$. `normalTargetChain` is the normal target process with known variance of Example 7.6 ($T = 0$, variance $1$, conjugate prior $N(\bar x, 1/n)$): the next observation is $\bar x + \sqrt{1 + 1/n}\,Z$ with $Z \sim N(0, 1)$ (the predictive $N(\bar x, 1 + 1/n)$ of (7.6)); if it is $\ge 0$ the target is reached, otherwise the state moves by `meanUpdate`; `normalTargetReward` is $P(\bar x + \sqrt{1+1/n}\,Z \ge 0) = \Phi(\bar x(1 + n^{-1})^{-1/2})$, $0$ in $C$. Both are built from a seed kernel rather than from a beta or normal prior kernel; their transition probabilities are the ones the book computes.
--
--   **Conventions.** Process time is $0, 1, 2, \dots$; the Gittins index is that of the Bandit Algorithms model (`gittinsIndex`) on these chains, with discount factor $a \in (0, 1)$; the book's discrete-time correction factor is not applied (it cancels in the invariance identities and in $\nu = r$).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, Chapter 7: §7.1 bandit sampling processes, (7.1)-(7.3), reward and target processes and the completion state (pp. 173-176), §7.3 favourable densities (p. 181), Examples 7.5-7.6 (pp. 182-183), §7.4 location and scale parameters and Corollaries 7.10, 7.12 (pp. 188-191)

import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_AllocationIndices_Restless

/-!
# Multi-armed Bandit Allocation Indices, Chapter 7: multi-population random sampling

Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices*, 2nd ed., Wiley 2011,
Chapter 7 (pp. 173–211).

**Bandit sampling processes (§7.1).** An arm generates i.i.d. observations `X₁, X₂, …` from a
distribution `f(· | θ)` with an unknown parameter `θ`, on which the decision maker holds a prior
`π₀`; after observing `x₁, …, xₙ` the posterior is `πₙ` (7.1). The *state* of the sampling process
is the current posterior; with a conjugate family of priors it is specified by the parameters of
the current distribution. Continuing the process samples the next `X` from the *predictive*
distribution `f(· | π) = ∫ f(· | θ) π(dθ)`, earns `r(S, π) = ∫ g(x) f(x | π) dμ₁(x)` (7.3), and moves
the state to the posterior. A **reward process** has `g(x) = x`; a **target process** with target
`T` has `g(x) = 𝟙{x ≥ T}` and a completion state `C`, reached when an observation reaches the
target, from which all further rewards are `0`; `r(S, π)` is then the *current probability of
success* (CPS).

**This module.** A `SamplingModel Θ P` is a likelihood kernel `Θ → ℝ`, a family of priors
`P → Θ` indexed by the parameters of a conjugate family, and the Bayes update map
`P → ℝ → P` of those parameters. `IsConjugate` says the update map really computes the
posterior (Mathlib's `posterior`, the Bayesian inverse of the likelihood kernel). `rewardChain`
and `targetChain` are the Markov chains of parameters of the reward and target processes, on
which the Gittins index of the *Bandit Algorithms* model is taken. Location and scale
parameters are as on pp. 188–189: `μ` is a location parameter if `f(· | μ + c)` is `f(· | μ)`
shifted by `c`, `σ > 0` a scale parameter if `f(· | bσ)` is `f(· | σ)` scaled by `b`; the prior
family with parameters `(x̄, n)` has `x̄` as a location (scale) parameter in the same sense, and
`meanUpdate` is the rule `(x̄, n) ↦ ((n x̄ + x)/(n + 1), n + 1)` of Corollaries 7.10 and 7.12.
`IsFavourable` is the property of §7.3 on which Proposition 7.4 rests. The Bernoulli target
process of Example 7.5 (states `(α, β)`, CPS `α/(α + β)`, an unsuccessful trial moving to
`(α, β + 1)`) and the normal target process with known variance of Example 7.6 (states
`(x̄, n)`, predictive `N(x̄, 1 + 1/n)`, update by `meanUpdate`) are built directly from a seed
kernel, as the book computes them.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-! ### Sampling models -/

section Sampling

variable {Θ P : Type*} [MeasurableSpace Θ] [MeasurableSpace P]

/-- A Bayesian sampling model (§7.1): the likelihood `f(· | θ)` as a Markov kernel, a family of
priors indexed by the parameters `P` of a conjugate family, and the update of those parameters
after one observation. -/
structure SamplingModel (Θ P : Type*) [MeasurableSpace Θ] [MeasurableSpace P] where
  /-- `f(· | θ)`, the distribution of one observation given the parameter. -/
  likelihood : Kernel Θ ℝ
  /-- The likelihood is a Markov kernel. -/
  likelihood_markov : IsMarkovKernel likelihood
  /-- `π(· | p)`, the prior (current) distribution of `θ` with parameters `p`. -/
  prior : Kernel P Θ
  /-- Each prior is a probability measure. -/
  prior_markov : IsMarkovKernel prior
  /-- The parameters after observing `x` in the state with parameters `p`. -/
  update : P → ℝ → P
  /-- The update is jointly measurable. -/
  measurable_update : Measurable (Function.uncurry update)

attribute [instance] SamplingModel.likelihood_markov SamplingModel.prior_markov

/-- The predictive distribution `f(· | π) = ∫ f(· | θ) π(dθ)` of the next observation in the state
with parameters `p`, as the kernel `likelihood ∘ₖ prior`. -/
noncomputable def SamplingModel.predictive (F : SamplingModel Θ P) : Kernel P ℝ :=
  F.likelihood ∘ₖ F.prior

instance SamplingModel.predictive.instIsMarkovKernel (F : SamplingModel Θ P) :
    IsMarkovKernel F.predictive := by
  unfold SamplingModel.predictive; infer_instance

/-- The family is **conjugate** with the stated update rule: for every `p` and predictive-almost
every observation `x`, the posterior of `π(· | p)` given `X = x` (the Bayesian inverse of the
likelihood, `posterior`) is `π(· | update p x)`; this is (7.1)–(7.2) for the parametrized family. -/
def SamplingModel.IsConjugate [StandardBorelSpace Θ] [Nonempty Θ] (F : SamplingModel Θ P) :
    Prop :=
  ∀ p, ∀ᵐ x ∂(F.predictive p), posterior F.likelihood (F.prior p) x = F.prior (F.update p x)

/-- The family is conjugate on the set `s` of admissible parameters: the conjugacy identity of
`IsConjugate` holds at every `p ∈ s`. For the parameters `(x̄, n)` of Corollaries 7.10, 7.12 and
7.18 the admissible set is `{n > 0}`: a proper prior has `n > 0` (the book's `n = 0` is the
improper prior of Theorems 7.9, 7.11 and 7.17), and at `n = −1` the update `(n x̄ + x)/(n + 1)`
divides by zero, where conjugacy together with a location parameter is impossible. -/
def SamplingModel.IsConjugateOn [StandardBorelSpace Θ] [Nonempty Θ] (F : SamplingModel Θ P)
    (s : Set P) : Prop :=
  ∀ p ∈ s, ∀ᵐ x ∂(F.predictive p), posterior F.likelihood (F.prior p) x = F.prior (F.update p x)

/-- The chain of states of the **reward process**: from `p`, sample `x` from the predictive
distribution and move to `update p x`. -/
noncomputable def SamplingModel.rewardChain (F : SamplingModel Θ P) : Kernel P P :=
  (Kernel.id ×ₖ F.predictive).map (Function.uncurry F.update)

instance SamplingModel.rewardChain.instIsMarkovKernel (F : SamplingModel Θ P) :
    IsMarkovKernel F.rewardChain :=
  Kernel.IsMarkovKernel.map _ F.measurable_update

/-- `r(S, π) = ∫ x f(x | π) dμ₁(x)`, the expected next observation, the reward of the reward
process in the state `p` (7.3). -/
noncomputable def SamplingModel.rewardOf (F : SamplingModel Θ P) (p : P) : ℝ :=
  ∫ x, x ∂(F.predictive p)

/-- One step of the **target process** with target `T` from a non-completed state: sample `x`; if
`x ≥ T` move to the completion state `C` (`Sum.inr ()`), otherwise to `update p x`. -/
noncomputable def SamplingModel.targetStep (F : SamplingModel Θ P) (T : ℝ) :
    Kernel P (P ⊕ Unit) :=
  (Kernel.id ×ₖ F.predictive).map
    (fun q : P × ℝ ↦ if T ≤ q.2 then Sum.inr () else Sum.inl (F.update q.1 q.2))

lemma SamplingModel.measurable_targetStepFun (F : SamplingModel Θ P) (T : ℝ) :
    Measurable (fun q : P × ℝ ↦ if T ≤ q.2 then (Sum.inr () : P ⊕ Unit)
      else Sum.inl (F.update q.1 q.2)) :=
  Measurable.ite (measurableSet_le measurable_const measurable_snd) measurable_const
    (measurable_inl.comp F.measurable_update)

instance SamplingModel.targetStep.instIsMarkovKernel (F : SamplingModel Θ P) (T : ℝ) :
    IsMarkovKernel (F.targetStep T) :=
  Kernel.IsMarkovKernel.map _ (F.measurable_targetStepFun T)

/-- The chain of states of the target process with target `T` on `P ⊕ Unit`: the completion
state `C = Sum.inr ()` is absorbing. -/
noncomputable def SamplingModel.targetChain (F : SamplingModel Θ P) (T : ℝ) :
    Kernel (P ⊕ Unit) (P ⊕ Unit) where
  toFun := Sum.elim (fun p ↦ F.targetStep T p) (fun _ ↦ Measure.dirac (Sum.inr ()))
  measurable' := (F.targetStep T).measurable.sumElim measurable_const

instance SamplingModel.targetChain.instIsMarkovKernel (F : SamplingModel Θ P) (T : ℝ) :
    IsMarkovKernel (F.targetChain T) := by
  constructor
  rintro (p | u)
  · exact (SamplingModel.targetStep.instIsMarkovKernel F T).isProbabilityMeasure p
  · exact Measure.dirac.isProbabilityMeasure

/-- The reward of the target process: the current probability of success
`r(S, π) = f(· | π)[T, ∞)` in a non-completed state, `0` in `C`. -/
noncomputable def SamplingModel.targetReward (F : SamplingModel Θ P) (T : ℝ) : P ⊕ Unit → ℝ :=
  Sum.elim (fun p ↦ (F.predictive p (Set.Ici T)).toReal) (fun _ ↦ 0)

/-- The state `p` is **favourable** for the target `T` (§7.3, p. 181): along every sequence of
observations below the target, the current probability of success never exceeds its initial
value. -/
def SamplingModel.IsFavourable (F : SamplingModel Θ P) (T : ℝ) (p : P) : Prop :=
  ∀ xs : List ℝ, (∀ x ∈ xs, x < T) →
    F.targetReward T (Sum.inl (xs.foldl F.update p)) ≤ F.targetReward T (Sum.inl p)

end Sampling

/-! ### Location and scale parameters (§7.4, pp. 188–189) -/

section Invariance

/-- `μ` is a **location parameter** of the likelihood: `f(· | μ + c)` is the image of `f(· | μ)`
under `x ↦ x + c`. -/
def HasLocationParameter (κ : Kernel ℝ ℝ) : Prop :=
  ∀ μ c : ℝ, κ (μ + c) = (κ μ).map (· + c)

/-- `σ > 0` is a **scale parameter** of the likelihood: `f(· | bσ)` is the image of `f(· | σ)` under
`x ↦ b x` for `b > 0`. -/
def HasScaleParameter (κ : Kernel ℝ ℝ) : Prop :=
  ∀ σ b : ℝ, 0 < b → κ (b * σ) = (κ σ).map (b * ·)

/-- In the prior family with parameters `(x̄, n)`, `x̄` is a location parameter: the prior with
parameters `(x̄ + c, n)` is the prior with parameters `(x̄, n)` shifted by `c` (Corollary 7.10). -/
def PriorHasLocationParameter (η : Kernel (ℝ × ℝ) ℝ) : Prop :=
  ∀ xb n c : ℝ, η (xb + c, n) = (η (xb, n)).map (· + c)

/-- In the prior family with parameters `(x̄, n)`, `x̄` is a scale parameter: the prior with
parameters `(b x̄, n)` is the prior with parameters `(x̄, n)` scaled by `b > 0` (Corollary 7.12). -/
def PriorHasScaleParameter (η : Kernel (ℝ × ℝ) ℝ) : Prop :=
  ∀ xb n b : ℝ, 0 < b → η (b * xb, n) = (η (xb, n)).map (b * ·)

/-- The update rule of the sample mean and the count: the parameters `(x̄, n)` become
`((n x̄ + x)/(n + 1), n + 1)` when `x` is the next value sampled (Corollaries 7.10, 7.12). -/
noncomputable def meanUpdate (p : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  ((p.2 * p.1 + x) / (p.2 + 1), p.2 + 1)

lemma measurable_meanUpdate : Measurable (Function.uncurry meanUpdate) := by
  unfold Function.uncurry meanUpdate; fun_prop

end Invariance

/-! ### Two target processes (Examples 7.5 and 7.6) -/

section Examples

/-- The uniform distribution on `[0, 1]`, the seed of the Bernoulli trial. -/
noncomputable def uniformUnit : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)

instance uniformUnit.instIsProbabilityMeasure : IsProbabilityMeasure uniformUnit :=
  ⟨by simp [uniformUnit]⟩

/-- One trial of the **Bernoulli target process** (Example 7.5, `T = 1`, beta prior with
parameters `(α, β)`): with the current probability of success `α/(α + β)` the target is reached
(`C`), otherwise the state moves to `(α, β + 1)`. Built from a uniform seed `u`: success iff
`u < α/(α + β)`. -/
noncomputable def bernoulliTargetStep : Kernel (ℝ × ℝ) ((ℝ × ℝ) ⊕ Unit) :=
  (Kernel.id ×ₖ Kernel.const (ℝ × ℝ) uniformUnit).map
    (fun q : (ℝ × ℝ) × ℝ ↦ if q.2 < q.1.1 / (q.1.1 + q.1.2) then (Sum.inr () : (ℝ × ℝ) ⊕ Unit)
      else Sum.inl (q.1.1, q.1.2 + 1))

lemma measurable_bernoulliTargetFun :
    Measurable (fun q : (ℝ × ℝ) × ℝ ↦ if q.2 < q.1.1 / (q.1.1 + q.1.2)
      then (Sum.inr () : (ℝ × ℝ) ⊕ Unit) else Sum.inl (q.1.1, q.1.2 + 1)) :=
  Measurable.ite (measurableSet_lt measurable_snd (by fun_prop)) measurable_const
    (measurable_inl.comp (by fun_prop))

instance bernoulliTargetStep.instIsMarkovKernel : IsMarkovKernel bernoulliTargetStep :=
  Kernel.IsMarkovKernel.map _ measurable_bernoulliTargetFun

/-- The chain of the Bernoulli target process on `(ℝ × ℝ) ⊕ Unit`, `C` absorbing. -/
noncomputable def bernoulliTargetChain : Kernel ((ℝ × ℝ) ⊕ Unit) ((ℝ × ℝ) ⊕ Unit) where
  toFun := Sum.elim (fun p ↦ bernoulliTargetStep p) (fun _ ↦ Measure.dirac (Sum.inr ()))
  measurable' := bernoulliTargetStep.measurable.sumElim measurable_const

instance bernoulliTargetChain.instIsMarkovKernel : IsMarkovKernel bernoulliTargetChain := by
  constructor
  rintro (p | u)
  · exact bernoulliTargetStep.instIsMarkovKernel.isProbabilityMeasure p
  · exact Measure.dirac.isProbabilityMeasure

/-- The current probability of success `r(α, β) = α/(α + β)` of the Bernoulli target process,
`0` in `C`. -/
noncomputable def bernoulliTargetReward : (ℝ × ℝ) ⊕ Unit → ℝ :=
  Sum.elim (fun p ↦ p.1 / (p.1 + p.2)) (fun _ ↦ 0)

/-- One trial of the **normal target process with known variance** (Example 7.6, `T = 0`,
variance `1`, conjugate prior `N(x̄, 1/n)`): the next observation is `x̄ + √(1 + 1/n) Z` with
`Z ~ N(0, 1)` (the predictive density (7.6) is `N(x̄, 1 + 1/n)`); if it is `≥ 0` the target is
reached, otherwise the state moves to `((n x̄ + x)/(n + 1), n + 1)`. -/
noncomputable def normalTargetStep : Kernel (ℝ × ℝ) ((ℝ × ℝ) ⊕ Unit) :=
  (Kernel.id ×ₖ Kernel.const (ℝ × ℝ) (gaussianReal 0 1)).map
    (fun q : (ℝ × ℝ) × ℝ ↦
      if 0 ≤ q.1.1 + Real.sqrt (1 + 1 / q.1.2) * q.2 then (Sum.inr () : (ℝ × ℝ) ⊕ Unit)
      else Sum.inl (meanUpdate q.1 (q.1.1 + Real.sqrt (1 + 1 / q.1.2) * q.2)))

lemma measurable_normalTargetFun :
    Measurable (fun q : (ℝ × ℝ) × ℝ ↦
      if 0 ≤ q.1.1 + Real.sqrt (1 + 1 / q.1.2) * q.2 then (Sum.inr () : (ℝ × ℝ) ⊕ Unit)
      else Sum.inl (meanUpdate q.1 (q.1.1 + Real.sqrt (1 + 1 / q.1.2) * q.2))) := by
  refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
    (measurable_inl.comp ?_)
  have h : Measurable (fun q : (ℝ × ℝ) × ℝ ↦ q.1.1 + Real.sqrt (1 + 1 / q.1.2) * q.2) := by
    fun_prop
  exact measurable_meanUpdate.comp (measurable_fst.prodMk h)

instance normalTargetStep.instIsMarkovKernel : IsMarkovKernel normalTargetStep :=
  Kernel.IsMarkovKernel.map _ measurable_normalTargetFun

/-- The chain of the normal target process on `(ℝ × ℝ) ⊕ Unit`, `C` absorbing. -/
noncomputable def normalTargetChain : Kernel ((ℝ × ℝ) ⊕ Unit) ((ℝ × ℝ) ⊕ Unit) where
  toFun := Sum.elim (fun p ↦ normalTargetStep p) (fun _ ↦ Measure.dirac (Sum.inr ()))
  measurable' := normalTargetStep.measurable.sumElim measurable_const

instance normalTargetChain.instIsMarkovKernel : IsMarkovKernel normalTargetChain := by
  constructor
  rintro (p | u)
  · exact normalTargetStep.instIsMarkovKernel.isProbabilityMeasure p
  · exact Measure.dirac.isProbabilityMeasure

/-- The current probability of success of the normal target process,
`r(x̄, n) = P(x̄ + √(1 + 1/n) Z ≥ 0) = Φ(x̄ (1 + n⁻¹)^{-1/2})` (7.6); `0` in `C`. -/
noncomputable def normalTargetReward : (ℝ × ℝ) ⊕ Unit → ℝ :=
  Sum.elim (fun p ↦ ((gaussianReal 0 1) {z | 0 ≤ p.1 + Real.sqrt (1 + 1 / p.2) * z}).toReal)
    (fun _ ↦ 0)

end Examples

end AllocationIndices


