-- Prove2me | Definitions.Def_IntroBandits_Model
-- name    : IntroBandits_Model
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T05:45:30.4603+00:00
-- url     : https://prove2.me/theorems/670bf036-f16e-4403-a254-2f96cd855bf9
-- title:
--   Stochastic bandits with $[0,1]$ rewards: regret $R(T)$, confidence radius, $\mathrm{UCB}_t$, $\mathrm{LCB}_t$ and the clean event
-- statement:
--   The basic model of Chapter 1 of Slivkins's *Introduction to Multi-Armed Bandits*, built on top of the platform's `BanditAlgorithm` model of Lattimore and Szepesvári, which describes the same protocol.
--
--   **Instance.** There are $K$ arms and $T$ rounds. Each arm $a$ has a reward distribution $D_a$ on the reals with mean $\mu(a) = \mathbb{E}[D_a]$; the best mean is $\mu^* = \max_a \mu(a)$ and the gap of arm $a$ is $\Delta(a) = \mu^* - \mu(a)$. An instance is a `StochasticBandit K` of the `BanditAlgorithm` series. Slivkins assumes per-round rewards lie in $[0,1]$; `RewardsInUnitInterval ν` says that every $D_a$ gives probability one to $[0,1]$.
--
--   **Protocol.** In each round $t$ the algorithm picks an arm $a_t$, a reward $r_t \sim D_{a_t}$ is drawn independently of everything else, and the algorithm observes $r_t$ and nothing else (bandit feedback). An algorithm is a `BanditPolicy K`: for each round, a Markov kernel from the observed history to the arm played, so randomized and adaptive algorithms are covered. The law of the length-$T$ history $(a_1, r_1), \dots, (a_T, r_T)$ is `banditMeasure ν π T`.
--
--   **Regret**, Eq. (1.1):
--   $$R(T) = \mu^* \cdot T - \sum_{t=1}^{T} \mu(a_t),$$
--   a random variable through the arms chosen (`realizedRegret`), and its expectation $\mathbb{E}[R(T)]$ under the interaction law (`expectedRegret`).
--
--   **Confidence bounds**, §1.3.1. For a round $t$ and an arm $a$, let $n_t(a)$ be the number of rounds before $t$ in which $a$ was chosen and $\bar\mu_t(a)$ the average reward observed in those rounds (the platform's `armPullCount` and `armEmpiricalMean` applied to the history so far). The confidence radius of Eq. (1.5) is
--   $$r_t(a) = \sqrt{2 \log(T) / n_t(a)},$$
--   and $\mathrm{UCB}_t(a) = \bar\mu_t(a) + r_t(a)$, $\mathrm{LCB}_t(a) = \bar\mu_t(a) - r_t(a)$.
--
--   **The clean event**, Eq. (1.6): $\mathcal{E} = \{\forall a\ \forall t:\ |\bar\mu_t(a) - \mu(a)| \le r_t(a)\}$, as a set of length-$T$ histories, where $t$ ranges over all rounds up to $T+1$ (so every prefix of the history is constrained).
--
--   These objects are shared by the whole series; every later mission on this book imports them.
--
--   **Formalization Note** Lean's convention $x/0 = 0$ makes the confidence radius of an arm never chosen equal to $0$ where the book has $+\infty$; accordingly the clean event only constrains arms with at least one pull, which is exactly the book's condition since an infinite radius makes it vacuous. Rounds are $0$-indexed inside Lean (round $t$ is played after $t$ completed rounds) and `historyPrefix h hs` is the history of the first $s$ rounds.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), Chapter 1: §1.1 pp. 4-5 (problem protocol, Remark 1.1, Eq. (1.1)); §1.3.1 pp. 8-9 (Eq. (1.5), UCB/LCB, Eq. (1.6))

import Definitions.Def_banditRegret

/-!
Slivkins, *Introduction to Multi-Armed Bandits* (arXiv:1904.07272, Foundations and Trends in
Machine Learning 12 (2019)), Chapter 1, §1.1 (pp. 4-5) and §1.3.1 (pp. 8-9).

The stochastic bandit model of §1.1 with rewards in `[0,1]`, the regret `R(T)` of Eq. (1.1) and
its expectation, and the confidence-bound apparatus of §1.3.1: the confidence radius
`r_t(a) = sqrt(2 log T / n_t(a))` of Eq. (1.5), the bounds `UCB_t(a)`, `LCB_t(a)`, and the clean
event `E` of Eq. (1.6).

The environment, the algorithm and the interaction law are those of the platform's
`BanditAlgorithm` series (Lattimore-Szepesvári §4.1, §4.6), which coincide with Slivkins's
protocol of §1.1: an instance is a `StochasticBandit K` (one reward distribution `D_a` per arm,
mean `μ(a) = banditArmMean`, best mean `μ* = banditOptimalMean`, gap `Δ(a) = banditGap`); an
algorithm is a `BanditPolicy K` (a Markov kernel per round from the observed history to the arm
played next, so randomized and adaptive algorithms are covered); `banditMeasure ν π T` is the law
of the length-`T` history `(a_1, r_1), …, (a_T, r_T)` where `r_t ~ D_{a_t}` independently;
`armPullCount a h` is `n(a)`, the number of rounds of `h` in which `a` was chosen, and
`armEmpiricalMean a h` is `μ̄(a)`, the average reward observed in those rounds (junk value `0` if
`a` was never chosen).
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

variable {K : ℕ}

/-- Slivkins §1.1, third assumption: "per-round rewards are bounded; the restriction to the
interval [0,1] is for simplicity". Every arm's reward distribution gives probability one to
`[0,1]`. -/
def RewardsInUnitInterval (ν : StochasticBandit K) : Prop :=
  ∀ a : Fin K, ν.P a (Set.Icc (0 : ℝ) 1) = 1

/-- The regret at round `T`, Eq. (1.1): `R(T) = μ* · T − ∑_{t=1}^T μ(a_t)`, as a function of the
realized history (it depends on the history only through the arms chosen). -/
noncomputable def realizedRegret (ν : StochasticBandit K) {T : ℕ} (h : BanditHistory K T) : ℝ :=
  T * banditOptimalMean ν - ∑ t, banditArmMean ν (h t).1

/-- The expected regret `E[R(T)]` of algorithm `π` on instance `ν` over `T` rounds (§1.1). -/
noncomputable def expectedRegret (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) : ℝ :=
  ∫ h, realizedRegret ν h ∂(banditMeasure ν π T)

/-- The history of the first `s` rounds of a history of `T ≥ s` rounds. -/
def historyPrefix {T : ℕ} (h : BanditHistory K T) {s : ℕ} (hs : s ≤ T) : BanditHistory K s :=
  fun i ↦ h (Fin.castLE hs i)

/-- The confidence radius of Eq. (1.5) with time horizon `T` for an arm chosen `n` times so far:
`sqrt(2 log(T) / n)`. In the book an arm never chosen has an infinite radius; here Lean's
convention `x / 0 = 0` makes the radius `0`, so every statement that consults it guards on
`0 < n`. -/
noncomputable def confidenceRadius (T : ℕ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log T / n)

/-- The upper confidence bound `UCB_t(a) = μ̄_t(a) + r_t(a)` (§1.3.1), computed from the history
`h` of the rounds before `t`. -/
noncomputable def ucb (T : ℕ) {t : ℕ} (a : Fin K) (h : BanditHistory K t) : ℝ :=
  armEmpiricalMean a h + confidenceRadius T (armPullCount a h)

/-- The lower confidence bound `LCB_t(a) = μ̄_t(a) − r_t(a)` (§1.3.1). -/
noncomputable def lcb (T : ℕ) {t : ℕ} (a : Fin K) (h : BanditHistory K t) : ℝ :=
  armEmpiricalMean a h - confidenceRadius T (armPullCount a h)

/-- The clean event `E` of Eq. (1.6) for horizon `T`:
`E = { ∀ a ∀ t, |μ̄_t(a) − μ(a)| ≤ r_t(a) }`, where `μ̄_t(a)` and `r_t(a)` are computed from the
rounds before `t`, for every `t ≤ T + 1`. Only arms already chosen are constrained: for an arm
never chosen the book's radius is infinite and the condition is vacuous. -/
def CleanEvent (ν : StochasticBandit K) (T : ℕ) : Set (BanditHistory K T) :=
  {h | ∀ (a : Fin K) (s : ℕ) (hs : s ≤ T), 0 < armPullCount a (historyPrefix h hs) →
      |armEmpiricalMean a (historyPrefix h hs) - banditArmMean ν a| ≤
        confidenceRadius T (armPullCount a (historyPrefix h hs))}

end IntroBandits


