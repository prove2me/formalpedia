-- Prove2me | Definitions.Def_ThompsonSampling
-- name    : ThompsonSampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-30T15:43:36.454203+00:00
-- url     : https://prove2.me/theorems/a32feb03-cb9b-4faa-99d1-4d8af72d64f1
-- statement:
--   Thompson sampling, both forms of L&S Ch 36.
--
--   **Frequentist** (§36.2, Algorithm 24 as instantiated in Theorem 36.3): `IsGaussianTSPolicy` says that each round the policy samples
--
--   $$\theta_i \sim \mathcal{N}\!\left(\hat\mu_i(t-1),\ \frac{1}{T_i(t-1)}\right)$$
--
--   independently per arm and plays the minimal-index argmax, with initial distributions $F_i(1) = \delta_\infty$ (so while some arm is unplayed, the least-index unplayed arm is played); the arm distribution is the pushforward of the product of the $k$ posterior Gaussians under the measurable min-index argmax map `minArgmax`. Also transcribes the §36.2 reward-stack quantities: $\hat\mu_{is}$ (mean of the first $s$ rewards of arm $i$) and the posterior tail probability $G_{is} = 1 - F_{is}(c)$ (`gaussianTSTailProb`).
--
--   **Bayesian adversarial** (§36.4): the joint law of a prior-drawn reward matrix $X \in [0,1]^{n\times k}$ and the interconnection history (`bayesianAdversarialMeasure`), the optimal action $A^* = \mathrm{argmax}_a \sum_t X_{ta}$, the Bayesian regret
--
--   $$BR_n = \mathbb{E}\Big[\sum_t (X_{tA^*} - X_{tA_t})\Big],$$
--
--   and `IsBayesianTSPolicy`:
--
--   $$\pi_t(\cdot \mid H_{t-1}) = \mathbb{P}(A^* \in \cdot \mid H_{t-1}) \quad\text{a.s.},$$
--
--   encoded as “the joint law of $(H_t, A^*)$ equals the comp-prod of the law of $H_t$ with the kernel $\pi_t$”.
-- source:
--   L&S Ch 36.2 (Algorithm 24, Thm 36.3 instantiation) and Ch 36.4, pp.463-469

import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 36:
Thompson sampling.

**Frequentist form (§36.2, Algorithm 24 as instantiated in Theorem 36.3).**
At round `t`, sample `θ_i ~ N(μ̂_i(t-1), 1/T_i(t-1))` independently for each arm
and play `argmax_i θ_i`. The initial distributions are `F_i(1) = δ_∞`, so an
arm that has never been played always wins the argmax: while some arm is
unplayed, the policy deterministically plays the least-index unplayed arm
(the systematic tie-break of Algorithm 23/24 resolving the `+∞` ties); once
every arm has been played, the arm distribution is the pushforward of the
product of the `k` posterior Gaussians under the (measurable) minimal-index
argmax map. `IsGaussianTSPolicy` characterizes this policy.

For the pull-count decomposition (Theorem 36.2) we also transcribe, for this
Gaussian instantiation, the §36.2 quantities `F_{is}`/`G_{is}`: `F_{is}` is the
CDF used for arm `i` in all rounds `t` with `T_i(t-1) = s`, i.e. the CDF of
`N(μ̂_{is}, 1/s)` where `μ̂_{is}` is the empirical mean of the first `s` rewards
of arm `i` (and `F_{i0} = δ_∞`), and `G_{is} = 1 - F_{is}(μ_1 - ε)` is the
posterior tail probability. The book defines `G_{is}` for all `s < n` via the
reward-stack model even when arm `i` is played fewer than `s` times; here
`armFirstRewardsMean` returns a junk value in that case, which is harmless in
Theorem 36.2 because the corresponding summands are then extra nonnegative
terms on the right-hand side.

**Bayesian adversarial form (§36.4).** The adversary's reward matrix
`X ∈ [0,1]^{n×k}` is drawn from a prior `Q`; the learner observes only
`X_{t,A_t}`. `bayesianAdversarialMeasure Q π t` is the joint law of `(X, H_t)`
(reward matrix and history of the first `t` rounds) under the interconnection
of the prior, the deterministic reward `X_{t,A_t}` and a policy `π`
(a `BanditPolicy k`, whose histories are exactly `H_t`). The optimal action is
`A* = argmax_a ∑_t X_{ta}` and the Bayesian regret is
`BR_n = E[∑_t (X_{tA*} - X_{tA_t})]`. Thompson sampling is characterized, as in
the book, by the almost-sure identity
`π_t(· | H_{t-1}) = ℙ(A* ∈ · | H_{t-1})`, encoded measure-theoretically:
the joint law of `(H_t, A*)` equals the composition-product of the law of `H_t`
with the kernel `π.select t`.
-/

open MeasureTheory ProbabilityTheory NNReal

/-! ### The minimal-index argmax -/

namespace BanditAlgorithm

/-- A real vector over the finite index set `Fin k`, `k ≥ 1`, attains its
maximum somewhere. -/
lemma argmaxSet_nonempty {k : ℕ} [NeZero k] (θ : Fin k → ℝ) :
    (Finset.univ.filter fun i : Fin k ↦ ∀ j, θ j ≤ θ i).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ θ
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, fun j ↦ hi j (Finset.mem_univ j)⟩⟩

/-- The minimal-index maximizer of a real vector `θ : Fin k → ℝ`
(the "arbitrary, but systematic" tie-break of L&S Algorithms 23/24). -/
noncomputable def minArgmax {k : ℕ} [NeZero k] (θ : Fin k → ℝ) : Fin k :=
  (Finset.univ.filter fun i : Fin k ↦ ∀ j, θ j ≤ θ i).min' (argmaxSet_nonempty θ)

lemma minArgmax_eq_iff {k : ℕ} [NeZero k] {θ : Fin k → ℝ} {i : Fin k} :
    minArgmax θ = i ↔ (∀ j, θ j ≤ θ i) ∧ ∀ j, (∀ l, θ l ≤ θ j) → i ≤ j := by
  constructor
  · rintro rfl
    constructor
    · have h := Finset.min'_mem
        (Finset.univ.filter fun i : Fin k ↦ ∀ j, θ j ≤ θ i) (argmaxSet_nonempty θ)
      exact (Finset.mem_filter.1 h).2
    · intro j hj
      exact Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
  · rintro ⟨h₁, h₂⟩
    refine le_antisymm (Finset.min'_le _ i (Finset.mem_filter.2 ⟨Finset.mem_univ i, h₁⟩)) ?_
    have h := Finset.min'_mem (Finset.univ.filter fun i : Fin k ↦ ∀ j, θ j ≤ θ i)
      (argmaxSet_nonempty θ)
    exact h₂ _ (Finset.mem_filter.1 h).2

/-- The minimal-index argmax is measurable. -/
lemma measurable_minArgmax {k : ℕ} [NeZero k] :
    Measurable (minArgmax : (Fin k → ℝ) → Fin k) := by
  apply measurable_to_countable'
  intro i
  have h : minArgmax ⁻¹' {i} =
      (⋂ j : Fin k, {θ : Fin k → ℝ | θ j ≤ θ i}) ∩
        ⋂ j : Fin k, {θ : Fin k → ℝ | (∀ l, θ l ≤ θ j) → i ≤ j} := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
    exact minArgmax_eq_iff
  rw [h]
  refine MeasurableSet.inter
    (MeasurableSet.iInter fun j ↦
      measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))
    (MeasurableSet.iInter fun j ↦ ?_)
  by_cases hij : i ≤ j
  · have : {θ : Fin k → ℝ | (∀ l, θ l ≤ θ j) → i ≤ j} = Set.univ := by
      ext θ
      simp [hij]
    rw [this]
    exact MeasurableSet.univ
  · have : {θ : Fin k → ℝ | (∀ l, θ l ≤ θ j) → i ≤ j} =
        (⋂ l : Fin k, {θ : Fin k → ℝ | θ l ≤ θ j})ᶜ := by
      ext θ
      simp [hij]
    rw [this]
    exact (MeasurableSet.iInter fun l ↦
      measurableSet_le (measurable_pi_apply l) (measurable_pi_apply j)).compl

/-! ### Gaussian Thompson sampling (Algorithm 24 for Theorem 36.3) -/

/-- The Thompson-sampling arm distribution given history `h` (L&S Algorithm 24
with `F_i(1) = δ_∞` and Gaussian updates `N(μ̂_i(t), 1/T_i(t))`, as in
Theorem 36.3): while some arm is unplayed, its sample is `+∞` and it wins the
argmax, so the least-index unplayed arm is played; once all arms have been
played, sample `θ_i ~ N(μ̂_i, 1/T_i)` independently and play the minimal-index
argmax. -/
noncomputable def gaussianTSDistribution {k : ℕ} [NeZero k] {n : ℕ}
    (h : BanditHistory k n) : Measure (Fin k) :=
  if ∃ i, armPullCount i h = 0 then
    Measure.dirac (minArgmax fun i ↦ if armPullCount i h = 0 then 1 else 0)
  else
    Measure.map minArgmax
      (Measure.pi fun i ↦ gaussianReal (armEmpiricalMean i h) ((armPullCount i h : ℝ≥0))⁻¹)

/-- `IsGaussianTSPolicy π`: the policy `π` is Thompson sampling with Gaussian
updates and initial distributions `δ_∞` (L&S Algorithm 24 as instantiated in
Theorem 36.3). -/
def IsGaussianTSPolicy {k : ℕ} [NeZero k] (π : BanditPolicy k) : Prop :=
  ∀ n (h : BanditHistory k n), (π.select n) h = gaussianTSDistribution h

/-! ### The reward-stack quantities `μ̂_{is}` and `G_{is}` of §36.2 -/

/-- The number of times arm `i` was played strictly before round `t` in
history `h`. -/
def armPullCountBefore {k n : ℕ} (i : Fin k) (t : Fin n) (h : BanditHistory k n) : ℕ :=
  (Finset.univ.filter fun t' : Fin n ↦ t' < t ∧ (h t').1 = i).card

/-- The empirical mean `μ̂_{is}` of the first `s` rewards received from arm `i`
in history `h` (the quantity fed to the CDF `F_{is}` of L&S §36.2): the sum of
the rewards observed in the rounds where arm `i` was played for the `1st, …,
s`-th time, divided by `s`. If arm `i` was played fewer than `s` times this is
a junk value (partial sum divided by `s`), matching the reward-stack
convention only on the event `T_i ≥ s` — which is all Theorem 36.2 needs. -/
noncomputable def armFirstRewardsMean {k n : ℕ} (i : Fin k) (s : ℕ)
    (h : BanditHistory k n) : ℝ :=
  (∑ t ∈ Finset.univ.filter
      (fun t : Fin n ↦ (h t).1 = i ∧ armPullCountBefore i t h < s), (h t).2) / s

/-- The tail probability `G_{is} = 1 - F_{is}(c)` of L&S §36.2 for the Gaussian
instantiation of Algorithm 24 (Theorem 36.3): the probability that arm `i`'s
perturbed sample exceeds `c` when arm `i` has been played `s` times, i.e. the
`(c, ∞)`-mass of the posterior `N(μ̂_{is}, 1/s)` for `s ≥ 1`, and `1` for
`s = 0` (since `F_{i0} = δ_∞`). -/
noncomputable def gaussianTSTailProb {k n : ℕ} (i : Fin k) (s : ℕ) (c : ℝ)
    (h : BanditHistory k n) : ℝ :=
  if s = 0 then 1
  else (gaussianReal (armFirstRewardsMean i s h) ((s : ℝ≥0))⁻¹).real {x | c < x}

/-! ### The Bayesian adversarial `k`-armed bandit (§36.4) -/

/-- One round of the Bayesian adversarial bandit: given the reward matrix `X`
and the history, sample the arm `A ~ π.select t` from the history alone and
receive the deterministic reward `X_{τ,A}` of round `τ`. -/
noncomputable def bayesianAdversarialStepKernel {k n : ℕ} (π : BanditPolicy k)
    (t : ℕ) (τ : Fin n) :
    Kernel ((Fin n → Fin k → ℝ) × BanditHistory k t) (Fin k × ℝ) :=
  ((π.select t).comap Prod.snd measurable_snd).compProd
    (Kernel.deterministic (fun p ↦ p.1.1 τ p.2)
      (measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp ((measurable_pi_apply τ).comp measurable_fst)))

instance bayesianAdversarialStepKernel.instIsMarkovKernel {k n : ℕ}
    (π : BanditPolicy k) (t : ℕ) (τ : Fin n) :
    IsMarkovKernel (bayesianAdversarialStepKernel π t τ) := by
  rw [bayesianAdversarialStepKernel]; infer_instance

/-- The joint law of the reward matrix and the history of the first `t` rounds
of the Bayesian adversarial bandit (L&S §36.4): `X ~ Q`, and in round `t` the
learner plays `A_t ~ π_t(· | H_{t-1})` and observes `X_{t,A_t}`. -/
noncomputable def bayesianAdversarialMeasure {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) (π : BanditPolicy k) :
    (t : ℕ) → t ≤ n → Measure ((Fin n → Fin k → ℝ) × BanditHistory k t)
  | 0, _ => Q.map (fun X ↦ (X, fun t ↦ t.elim0))
  | t + 1, ht =>
      ((bayesianAdversarialMeasure Q π t (Nat.le_of_succ_le ht)).compProd
          (bayesianAdversarialStepKernel π t ⟨t, ht⟩)).map
        (fun p ↦ (p.1.1, Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1.2 p.2))

instance bayesianAdversarialMeasure.instIsProbabilityMeasure {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (π : BanditPolicy k) (t : ℕ) (ht : t ≤ n) :
    IsProbabilityMeasure (bayesianAdversarialMeasure Q π t ht) := by
  induction t with
  | zero =>
      rw [bayesianAdversarialMeasure]
      exact Measure.isProbabilityMeasure_map
        (measurable_id.prodMk measurable_const).aemeasurable
  | succ t ih =>
      rw [bayesianAdversarialMeasure]
      haveI := ih (Nat.le_of_succ_le ht)
      exact Measure.isProbabilityMeasure_map
        ((measurable_fst.comp measurable_fst).prodMk
          (measurable_banditHistorySnoc.comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).aemeasurable

/-- The optimal action `A* = argmax_{a ∈ [k]} ∑_{t=1}^n X_{ta}` of the
Bayesian adversarial bandit (ties broken by the same systematic minimal-index
rule as in the algorithm). -/
noncomputable def bayesianOptimalAction {k n : ℕ} [NeZero k]
    (X : Fin n → Fin k → ℝ) : Fin k :=
  minArgmax fun a ↦ ∑ t, X t a

/-- The Bayesian regret `BR_n = E[∑_{t=1}^n (X_{tA*} - X_{tA_t})]` of a policy
for the Bayesian adversarial bandit with prior `Q` (L&S §36.4). -/
noncomputable def bayesianAdversarialRegret {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) (π : BanditPolicy k) : ℝ :=
  ∫ p, (∑ t, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1)))
    ∂bayesianAdversarialMeasure Q π n le_rfl

/-- `IsBayesianTSPolicy Q π`: Thompson sampling for the Bayesian adversarial
bandit (L&S §36.4): at every round `t`, the conditional law of the played arm
given the history equals the posterior law of the optimal arm,
`π_t(· | A_1, X_{1,A_1}, …, A_{t-1}, X_{t-1,A_{t-1}}) = ℙ(A* ∈ · | …)` a.s.
Encoded: the joint law of `(H_t, A*)` under the interconnection measure is the
composition-product of the law of `H_t` with the kernel `π.select t`. -/
def IsBayesianTSPolicy {k n : ℕ} [NeZero k] (Q : Measure (Fin n → Fin k → ℝ))
    (π : BanditPolicy k) : Prop :=
  ∀ (t : ℕ) (ht : t ≤ n),
    Measure.map
        (fun p ↦ ((fun s : Fin t ↦ p.2 (Fin.castLE ht s)), bayesianOptimalAction p.1))
        (bayesianAdversarialMeasure Q π n le_rfl) =
      (Measure.map (fun p ↦ fun s : Fin t ↦ p.2 (Fin.castLE ht s))
          (bayesianAdversarialMeasure Q π n le_rfl)).compProd (π.select t)

end BanditAlgorithm


