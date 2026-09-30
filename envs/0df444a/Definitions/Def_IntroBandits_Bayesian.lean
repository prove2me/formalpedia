-- Prove2me | Definitions.Def_IntroBandits_Bayesian
-- name    : IntroBandits_Bayesian
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T15:32:44.691889+00:00
-- url     : https://prove2.me/theorems/a1a7e76b-d955-4e94-95f2-6ea4f1817787
-- title:
--   Bayesian bandits: reward families, priors with finite support, the posterior $P_H$, Thompson Sampling and Bayesian regret
-- statement:
--   The Bayesian bandit model of Chapter 3 of Slivkins's *Introduction to Multi-Armed Bandits*, on top of the model of Mission I, with the chapter's three simplifications built in.
--
--   **Reward family.** A `RewardFamily` is a single-parameter family $(D_\nu)_{\nu}$ of probability distributions on the reals, fixed and known to the algorithm, such that $D_\nu$ has expectation $\nu$ for every $\nu \in [0,1]$ and realized rewards take only finitely many values (a finite set `values` carries all the mass of every $D_\nu$). A problem instance is then specified by its mean reward vector $\mu \in [0,1]^K$: `instanceOf fam μ` is the stochastic bandit whose arm $a$ has reward distribution $D_{\mu(a)}$.
--
--   **Prior and joint law.** The prior $\mathcal{P}$ is a probability measure on mean vectors with a finite support $F$ (a hypothesis $\mathcal{P}(F^c) = 0$ of the theorems). `jointMeasure P F fam π t` is the joint law of $(\mu, H_t)$: $\mu \sim \mathcal{P}$, then $H_t = ((a_1, r_1), \dots, (a_t, r_t))$ is the $t$-history of algorithm $\pi$ on the instance with mean vector $\mu$; explicitly $\sum_{\tilde\mu \in F} \mathcal{P}(\tilde\mu)\,\delta_{\tilde\mu} \otimes \mathbb{P}_{\tilde\mu,\pi}$. `historyProb` is $\Pr[H_t = H]$ and `condProb P F fam π H M` is the conditional probability $\Pr[\mu \in M \mid H_t = H]$ of Eq. (3.3), as the ratio of joint probabilities (junk $0$ when $\Pr[H_t = H] = 0$).
--
--   **Likelihood, feasibility and the posterior.** For a fixed $t$-history $H$, `likelihood fam μ H` $= \prod_{s \le t} D_{\mu(a'_s)}(\{r'_s\})$ is $\Pr[H_t = H \mid \mu]$ for the $H$-induced algorithm, which plays the arms of $H$ deterministically. `evidence P F fam H` $= \sum_{\tilde\mu \in F}\mathcal{P}(\tilde\mu)\Pr[H_t = H \mid \mu = \tilde\mu]$ is the probability of $H$ under that algorithm; $H$ is **feasible** (`IsFeasible`) when it is positive, which is the book's definition ($\Pr[H_t = H] > 0$ for some algorithm). The posterior $P_H$ (`posterior P F fam H`) is defined by Bayes' rule, Eq. (3.11):
--   $$P_H(\tilde\mu) = \frac{\mathcal{P}(\tilde\mu)\,\Pr[H_t = H \mid \mu = \tilde\mu]}{\sum_{\tilde\mu \in F} \mathcal{P}(\tilde\mu)\,\Pr[H_t = H \mid \mu = \tilde\mu]}, \qquad \tilde\mu \in F,$$
--   the zero measure when $H$ is infeasible. Lemma 3.1 (a theorem of this mission) says this is $\Pr[\mu \in \cdot \mid H_t = H]$ for every algorithm under which $H$ has positive probability.
--
--   **Thompson Sampling.** `IsBestArm μ a` says $\mu(a) = \max_b \mu(b)$. `IsThompsonSampling P F fam π` is Algorithm 3.1: for every feasible history $H$ of the rounds so far and every arm $a$, the algorithm draws $a$ with probability $p_t(a \mid H) = \Pr[a^* = a \mid H_{t-1} = H] = P_H\{\mu : a \text{ is a best arm of } \mu\}$. `IsThompsonSamplingAlt P F fam π` is Algorithm 3.2: there is a measurable rule `best` picking a best arm of every $\mu \in F$ such that, for every feasible $H$, the arm played is `best`$(\mu_t)$ for a sample $\mu_t \sim P_H$.
--
--   **Bayesian regret**, Eq. (3.1): $BR(T) = \mathbb{E}_{\mu \sim \mathcal{P}}\big[\mathbb{E}[R(T) \mid \mu]\big] = \sum_{\mu \in F}\mathcal{P}(\mu)\,\mathbb{E}[R(T) \mid \mu]$ (`bayesianRegret`), with $\mathbb{E}[R(T)\mid\mu]$ the expected regret of Mission I on `instanceOf fam μ`.
--
--   **Independent priors** (§3.1.4). `armLikelihood fam a H x` $= \prod_{s : a'_s = a} D_x(\{r'_s\})$ is the likelihood of the projected history $\mathrm{proj}(H; a)$ when arm $a$ has mean $x$, and `armPosterior P F fam a H` is the posterior $P^a_H$ of the single mean reward $\mu(a)$ given $\mathrm{proj}(H; a)$, Eq. (3.10), by Bayes' rule with that likelihood; it is a measure on $\mathbb{R}$.
--
--   **Formalization Note** Histories are $0$-indexed inside Lean; a "$t$-history" is a `BanditHistory K t`. Because the prior has finite support and rewards take finitely many values, every joint law is carried by finitely many points, so all expectations in this mission are finite sums and no integrability side conditions are needed. The uniqueness of the best arm on $F$ (the chapter's third simplification) is a hypothesis of the theorems that need it, not part of the definitions.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), Chapter 3: p. 27 (Bayesian regret, Eq. (3.1), the three simplifications), §3.1.1 p. 28 (t-histories, feasible histories, the H-induced algorithm, Eq. (3.3)), Eq. (3.11) p. 32 (Bayes' rule for P_H), §3.1.4 p. 31 (projected histories, Eq. (3.10)), Algorithms 3.1 and 3.2 p. 32

import Mathlib.Probability.Independence.Basic
import Definitions.Def_IntroBandits_Model

/-!
Slivkins, *Introduction to Multi-Armed Bandits* (arXiv:1904.07272), Chapter 3 (pp. 27-34):
Bayesian bandits and Thompson Sampling.

The chapter's simplifications (p. 27) are built in: rewards come from a known single-parameter
family `(D_ν)` of distributions with mean `ν`, realized rewards take finitely many values, the
prior `P` on mean vectors `μ ∈ [0,1]^K` has a finite support `F`, and (as a hypothesis of the
theorems) the best arm is unique on `F`.

* `RewardFamily` — the family `(D_ν)_{ν}`: probability measures on `ℝ` supported on a finite set
  of values, with mean `ν` for `ν ∈ [0,1]`; `instanceOf fam μ` is the stochastic bandit with
  reward distribution `D_{μ(a)}` at arm `a`.
* `jointMeasure P F fam π t` — the joint law of `(μ, H_t)`: `μ ~ P` (supported on `F`), then the
  `t`-history of algorithm `π` on `instanceOf fam μ`. `historyProb` is `Pr[H_t = H]` and
  `condProb` is `Pr[μ ∈ M | H_t = H]`, the posterior of Eq. (3.3) as a ratio of probabilities.
* `likelihood fam μ H` is `Pr[H_t = H | μ]` for the `H`-induced algorithm (§3.1.1), and
  `posterior P F fam H` is the Bayesian posterior `P_H` computed by Bayes' rule, Eq. (3.11):
  `P_H(μ̃) = P(μ̃) Pr[H_t = H | μ = μ̃] / ∑_{μ̃ ∈ F} P(μ̃) Pr[H_t = H | μ = μ̃]`.
  A history is `IsFeasible` when this denominator is positive (Pr[H_t = H] > 0 for the
  `H`-induced algorithm).
* `IsThompsonSampling P F fam π` — Algorithm 3.1 (p. 32): in each round the arm `a` is drawn with
  probability `p_t(a | H) = Pr[a* = a | H_{t-1} = H] = P_H{μ : a is a best arm of μ}`.
  `IsThompsonSamplingAlt` is the alternative characterization, Algorithm 3.2: sample `μ_t ~ P_H`
  and play a best arm of `μ_t`.
* `bayesianRegret P F fam π T` — `BR(T) = E_{μ ~ P}[E[R(T) | μ]]`, Eq. (3.1).
* `armLikelihood`, `armPosterior` — for independent priors (§3.1.4): the posterior `P^a_H` of
  the single mean reward `μ(a)` given the projected history `proj(H; a)`, Eq. (3.10), written
  with the projected history's likelihood `∏_{s : a_s = a} D_{μ(a)}({r_s})`.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

/-- A single-parameter family of reward distributions `(D_ν)` (p. 27): `D_ν` is a probability
distribution on `ℝ` with expectation `ν` (for `ν ∈ [0,1]`), and realized rewards take only
finitely many values. -/
structure RewardFamily where
  /-- The reward distribution with parameter `ν`. -/
  D : ℝ → Measure ℝ
  /-- Each `D_ν` is a probability measure. -/
  prob : ∀ ν, IsProbabilityMeasure (D ν)
  /-- The finite set of values a realized reward can take. -/
  values : Finset ℝ
  /-- Rewards take values in `values` almost surely. -/
  supp : ∀ ν, D ν (↑values)ᶜ = 0
  /-- `D_ν` has expectation `ν` for every `ν ∈ [0,1]`. -/
  mean : ∀ ν ∈ Set.Icc (0 : ℝ) 1, ∫ x, x ∂(D ν) = ν

attribute [instance] RewardFamily.prob

variable {K : ℕ}

/-- The problem instance with mean reward vector `μ`: arm `a` has reward distribution
`D_{μ(a)}`. -/
def instanceOf (fam : RewardFamily) (μ : Fin K → ℝ) : StochasticBandit K where
  P a := fam.D (μ a)
  prob a := fam.prob (μ a)

/-- The joint law of the mean vector `μ ~ P` (a prior supported on the finite set `F`) and the
`t`-history `H_t` of algorithm `π` run on the instance with mean vector `μ`. -/
noncomputable def jointMeasure (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) (π : BanditPolicy K) (t : ℕ) :
    Measure ((Fin K → ℝ) × BanditHistory K t) :=
  ∑ μ ∈ F, P {μ} • (Measure.dirac μ).prod (banditMeasure (instanceOf fam μ) π t)

/-- `Pr[H_t = H]` under the joint law. -/
noncomputable def historyProb (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) (π : BanditPolicy K) {t : ℕ} (H : BanditHistory K t) : ENNReal :=
  jointMeasure P F fam π t (Set.univ ×ˢ {H})

/-- `Pr[μ ∈ M | H_t = H]`, Eq. (3.3): the posterior distribution given the history `H`, as a
ratio of joint probabilities (junk value `0` when `Pr[H_t = H] = 0`). -/
noncomputable def condProb (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) (π : BanditPolicy K) {t : ℕ} (H : BanditHistory K t)
    (M : Set (Fin K → ℝ)) : ENNReal :=
  jointMeasure P F fam π t (M ×ˢ {H}) / historyProb P F fam π H

/-- `Pr[H_t = H | μ]` for the `H`-induced algorithm, which plays the arms of `H`
deterministically: the product over rounds of the probabilities of the observed rewards. -/
noncomputable def likelihood (fam : RewardFamily) (μ : Fin K → ℝ) {t : ℕ}
    (H : BanditHistory K t) : ENNReal :=
  ∏ s, fam.D (μ (H s).1) {(H s).2}

/-- The normalizer of Bayes' rule, `∑_{μ̃ ∈ F} P(μ̃) Pr[H_t = H | μ = μ̃]`: the probability of
`H` under the `H`-induced algorithm. -/
noncomputable def evidence (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) {t : ℕ} (H : BanditHistory K t) : ENNReal :=
  ∑ μ ∈ F, P {μ} * likelihood fam μ H

/-- A feasible `t`-history (§3.1.1): `Pr[H_t = H] > 0` for the `H`-induced algorithm. -/
def IsFeasible (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ)) (fam : RewardFamily)
    {t : ℕ} (H : BanditHistory K t) : Prop :=
  evidence P F fam H ≠ 0

/-- The Bayesian posterior `P_H` after observing `H`, by Bayes' rule, Eq. (3.11):
`P_H(μ̃) = P(μ̃) Pr[H_t = H | μ = μ̃] / ∑_{μ̃ ∈ F} P(μ̃) Pr[H_t = H | μ = μ̃]`
(the zero measure when `H` is not feasible). -/
noncomputable def posterior (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) {t : ℕ} (H : BanditHistory K t) : Measure (Fin K → ℝ) :=
  ∑ μ ∈ F, (P {μ} * likelihood fam μ H / evidence P F fam H) • Measure.dirac μ

/-- `a` is a best arm of the mean vector `μ`: `μ(a) = max_b μ(b)`. -/
def IsBestArm (μ : Fin K → ℝ) (a : Fin K) : Prop :=
  ∀ b, μ b ≤ μ a

/-- `IsThompsonSampling P F fam π` (Algorithm 3.1, p. 32): for every feasible history `H` of
the rounds so far, the arm `a` is drawn with probability `p_t(a | H) = Pr[a* = a | H]`, the
posterior probability that `a` is the best arm. -/
def IsThompsonSampling (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ)) (fam : RewardFamily)
    (π : BanditPolicy K) : Prop :=
  ∀ t (H : BanditHistory K t), IsFeasible P F fam H →
    ∀ a : Fin K, (π.select t) H {a} = posterior P F fam H {μ | IsBestArm μ a}

/-- `IsThompsonSamplingAlt P F fam π` (Algorithm 3.2, p. 32, the alternative characterization):
there is a measurable selection `best` of a best arm for every mean vector in `F` such that, for
every feasible history `H`, the arm played is `best μ_t` for a sample `μ_t ~ P_H`. -/
def IsThompsonSamplingAlt (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) (π : BanditPolicy K) : Prop :=
  ∃ best : (Fin K → ℝ) → Fin K, Measurable best ∧ (∀ μ ∈ F, IsBestArm μ (best μ)) ∧
    ∀ t (H : BanditHistory K t), IsFeasible P F fam H →
      (π.select t) H = (posterior P F fam H).map best

/-- Bayesian regret, Eq. (3.1): `BR(T) = E_{μ ~ P}[E[R(T) | μ]]`, the expected regret of
Eq. (1.1) averaged over the prior (supported on `F`). -/
noncomputable def bayesianRegret (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) (π : BanditPolicy K) (T : ℕ) : ℝ :=
  ∑ μ ∈ F, (P {μ}).toReal * expectedRegret (instanceOf fam μ) π T

/-- The likelihood of the projected history `proj(H; a)` (§3.1.4) when arm `a` has mean `x`:
`∏_{s : a_s = a} D_x({r_s})`. -/
noncomputable def armLikelihood (fam : RewardFamily) (a : Fin K) {t : ℕ}
    (H : BanditHistory K t) (x : ℝ) : ENNReal :=
  ∏ s ∈ Finset.univ.filter (fun s ↦ (H s).1 = a), fam.D x {(H s).2}

/-- The posterior `P^a_H` of the mean reward `μ(a)` given the projected history `proj(H; a)`,
Eq. (3.10), by Bayes' rule with the projected history's likelihood: a measure on `ℝ`. -/
noncomputable def armPosterior (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ))
    (fam : RewardFamily) (a : Fin K) {t : ℕ} (H : BanditHistory K t) : Measure ℝ :=
  ∑ μ ∈ F, (P {μ} * armLikelihood fam a H (μ a) /
      ∑ μ' ∈ F, P {μ'} * armLikelihood fam a H (μ' a)) • Measure.dirac (μ a)

end IntroBandits


