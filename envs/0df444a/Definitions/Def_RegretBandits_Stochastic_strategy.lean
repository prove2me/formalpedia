-- Prove2me | Definitions.Def_RegretBandits_Stochastic_strategy
-- name    : RegretBandits_Stochastic_strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:03:48.100577+00:00
-- url     : https://prove2.me/theorems/372b9a25-cb54-464b-9bed-9da7636b13cb
-- title:
--   Randomized bandit strategies and Bernoulli bandits
-- statement:
--   **Strategies.** A (possibly randomized) strategy for $K$ arms is a family of measurable rules $\pi_t$: before round $t+1$ the forecaster has seen the history $h_t=((I_1,Y_1),\dots,(I_t,Y_t))$ of arms played and rewards received, draws a fresh seed $u$, and plays $I_{t+1}=\pi_t(h_t,u)$. With a seed uniform on $[0,1]$, every randomized rule mapping histories to distributions over the arms has this form. The strategy does not know the horizon.
--
--   **Run of a strategy.** On a reward stack $X_{i,k}$ (the reward of the $(k+1)$-st pull of arm $i$) and seeds $U_1,U_2,\dots$, round $t+1$ plays $I_{t+1}=\pi_t(h_t,U_{t+1})$, and the reward it reports is $X_{I_{t+1},k}$, where $k$ is the number of earlier rounds that played $I_{t+1}$.
--
--   **Bernoulli bandit.** For $\mu=(\mu_1,\dots,\mu_K)\in[0,1]^K$, a Bernoulli bandit on a probability space $(\Omega,\mathbb P)$ is a reward stack in which $X_{i,k}$ is Bernoulli with mean $\mu_i$ (values in $\{0,1\}$), seeds $U_t$ uniform on $[0,1]$, and all rewards and seeds mutually independent.
--
--   These are the objects of the lower bound, Theorem 2.2, which quantifies over every strategy and every Bernoulli bandit.
--
--   **Formalization Note.** The arm played at round $t\ge1$ is `strategyArm π X U t ω`; its value at $t=0$ is a junk value that is never used.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 4 (protocol box), p. 12–13, Section 2.3

import Mathlib

namespace RegretBandits.Stochastic

open MeasureTheory ProbabilityTheory

/-- A (possibly randomized, horizon-free) forecaster for the `K`-armed stochastic bandit
(Bubeck and Cesa-Bianchi, arXiv:1204.5721v2, protocol of p. 4): before round `t + 1` it has
observed the history `h : Fin t → Fin K × ℝ` (arm played and reward received in rounds
`1, …, t`), draws a fresh seed `u ∈ ℝ` and plays `choose t h u`. Every randomized rule mapping
histories to distributions on the arms has this form with `u` uniform on `[0, 1]`. The rule is
jointly measurable, so that the arms played are random variables. -/
structure Strategy (K : ℕ) where
  choose : (t : ℕ) → (Fin t → Fin K × ℝ) → ℝ → Fin K
  measurable_choose : ∀ t, Measurable (fun p : (Fin t → Fin K × ℝ) × ℝ => choose t p.1 p.2)

/-- The history after the arms `a 0, …, a (t-1)` (rounds `1, …, t`) have been played on the
reward stack `x`: round `s + 1` reports the arm `a s` and the reward `x (a s) k`, where `k` is the
number of earlier rounds `r < s` that played the same arm (stack-of-rewards representation:
`x i k` is the reward of the `(k + 1)`-st pull of arm `i`). -/
def history {K t : ℕ} (x : Fin K → ℕ → ℝ) (a : Fin t → Fin K) : Fin t → Fin K × ℝ :=
  fun s => (a s, x (a s) ((Finset.univ.filter (fun r : Fin t => r < s ∧ a r = a s)).card))

/-- The arms played in rounds `1, …, t` by the strategy `π` on the reward stack `x` with seeds
`u` (round `s + 1` uses the seed `u (s + 1)`). -/
def runPrefix {K : ℕ} (π : Strategy K) (x : Fin K → ℕ → ℝ) (u : ℕ → ℝ) :
    (t : ℕ) → Fin t → Fin K
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (α := fun _ => Fin K) (runPrefix π x u t)
      (π.choose t (history x (runPrefix π x u t)) (u (t + 1)))

/-- `strategyArm π X U t ω` is the arm `I_t` played by `π` in round `t ≥ 1` on the outcome `ω`
(reward stack `X · · ω`, seeds `U · ω`). The value at `t = 0` is the junk value `I_1` and is never
used (pull counts and pseudo-regret only look at rounds `t + 1`). -/
def strategyArm {Ω : Type*} {K : ℕ} (π : Strategy K) (X : Fin K → ℕ → Ω → ℝ) (U : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : Fin K :=
  runPrefix π (fun i k => X i k ω) (fun s => U s ω) (t + 1) ⟨t - 1, by omega⟩

/-- The Bernoulli distribution of parameter `p` as a measure on `ℝ`:
`p δ_1 + (1 - p) δ_0`. -/
noncomputable def bernoulliReal (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

/-- A Bernoulli bandit with mean vector `μ ∈ [0, 1]^K` (Section 2.3, p. 12) carried by the
probability space `(Ω, P)`, together with the forecaster's seeds: `X i k` (the reward of the
`(k + 1)`-st pull of arm `i`) has law `Bernoulli(μ i)`, each seed `U t` is uniform on `[0, 1]`, and
all rewards and seeds are mutually independent. -/
structure IsBernoulliModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (μ : Fin K → ℝ) (X : Fin K → ℕ → Ω → ℝ) (U : ℕ → Ω → ℝ) : Prop where
  mean_mem : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1
  measurable_X : ∀ i k, Measurable (X i k)
  law_X : ∀ i k, P.map (X i k) = bernoulliReal (μ i)
  measurable_U : ∀ t, Measurable (U t)
  law_U : ∀ t, P.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1)
  indep : iIndepFun (Sum.elim (fun p : Fin K × ℕ => X p.1 p.2) U) P

end RegretBandits.Stochastic


