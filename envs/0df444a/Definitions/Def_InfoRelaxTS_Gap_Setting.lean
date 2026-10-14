-- Prove2me | Definitions.Def_InfoRelaxTS_Gap_Setting
-- name    : InfoRelaxTS_Gap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:38.772983+00:00
-- url     : https://prove2.me/theorems/85feb916-291f-4b37-9def-76965a5f56b5
-- title:
--   §2.1–§2.4, §3.1–§3.3, pp. 4–20 — Bayesian NEF bandit, outcome law (4), μ̂ (10)/(13), W^TS (29), W^IRS.FH (33), W^IRS.V-Zero (37), TS / IRS.FH / IRS.V-Zero, V (7)
-- statement:
--   This file sets up the Bayesian multi-armed bandit of Min, Maglaras and Moallemi with natural-exponential-family rewards and conjugate priors, together with the three performance bounds and the three randomized policies whose suboptimality gaps Theorem 3 controls.
--
--   **Instance.** There are $K$ arms $\mathcal A=\{1,\dots,K\}$. Arm $a$ carries a reference measure $h_a$ on $\mathbb R$ and a log-partition function $A_a:\mathbb R\to\mathbb R$; the instance is *normalized* when $\int e^{\theta r}\,h_a(dr)=e^{A_a(\theta)}$ for every $\theta\in\mathbb R$. Given the parameter $\theta_a$, the rewards $R_{a,1},R_{a,2},\dots$ of arm $a$ are i.i.d. with law (11)
--   $$\mathcal R_a(\theta_a)(dr)=h_a(dr)\,\exp\big(\theta_a r-A_a(\theta_a)\big).$$
--   A belief of arm $a$ is a pair $y_a=(\xi_a,\nu_a)$, and the conjugate prior (12) is
--   $$\mathcal P_a(\xi_a,\nu_a)(d\theta)=f_a(\xi_a,\nu_a)\,e^{\xi_a\theta-\nu_a A_a(\theta)}\,d\theta,\qquad \frac1{f_a(\xi_a,\nu_a)}=\int_{\mathbb R}e^{\xi_a\theta-\nu_a A_a(\theta)}\,d\theta .$$
--   The prior is *proper* at $(\xi_a,\nu_a)$ when $\nu_a>0$ and this integral is finite. The Bayesian update (13) is $\mathcal U_a((\xi,\nu),r)=(\xi+r,\nu+1)$, and the predictive law of the next reward under belief $y_a$ draws $\theta\sim\mathcal P_a(y_a)$ and then $r\sim\mathcal R_a(\theta)$. The family is $L$-smooth (59) when every $A_a$ is twice continuously differentiable with $A_a''\le L$ on $\mathbb R$.
--
--   **Means.** $\mu_a(\theta)=\int r\,\mathcal R_a(\theta)(dr)$ is the conditional mean reward and $\bar\mu_a(y_a)=\int\mu_a\,d\mathcal P_a(y_a)$ the predictive mean (9). The outcome $\omega=(\theta,(R_{a,n}))$ has law $\mathcal I(y)$ (4): arms are independent, $\theta_a\sim\mathcal P_a(y_a)$, and the rewards of arm $a$ are i.i.d. $\mathcal R_a(\theta_a)$ given $\theta_a$. The posterior predictive mean after the first $n$ rewards of arm $a$ is (10), computed through the conjugate update (13):
--   $$\hat\mu_{a,n}(\omega;y_a)=\bar\mu_a\Big(\xi_a+\sum_{i=1}^{n}R_{a,i},\ \nu_a+n\Big).$$
--
--   **Bounds.** With $\mathcal N_T=\{n\in\mathbb N_0^K:\sum_a n_a=T\}$ and $S_{a,n}=\sum_{i=1}^n\hat\mu_{a,i-1}$,
--   $$W^{\rm TS}(T,y)=\mathbb E_y\Big[T\max_a\mu_a(\theta_a)\Big],\quad W^{\rm IRS.FH}(T,y)=\mathbb E_y\Big[T\max_a\hat\mu_{a,T-1}\Big],\quad W^{\rm IRS.V\text{-}Zero}(T,y)=\mathbb E_y\Big[\max_{n\in\mathcal N_T}\sum_a S_{a,n_a}\Big],$$
--   which are (29), (33) and (37).
--
--   **Policies.** A policy maps the remaining horizon $T$ and the current belief $y$ to the law of the action it takes. Thompson sampling (Algorithm 2) samples $\tilde\theta\sim\mathcal P(y)$ and plays $\arg\max_a\mu_a(\tilde\theta_a)$; IRS.FH (Algorithm 4) samples $\tilde\omega\sim\mathcal I(y)$ and plays $\arg\max_a\hat\mu_{a,T-1}(\tilde\omega)$; IRS.V-Zero (§3.3) samples $\tilde\omega\sim\mathcal I(y)$, computes an optimal allocation $\tilde n^*\in\mathcal N_T$ of (37) and plays $\arg\max_a\tilde n^*_a$. Ties are broken by arbitrary selectors. The policies see only their own samples, never the true outcome. The Bayesian performance $V(\pi,T,y)$ of (7) is defined by the outer loop of Algorithms 1 and 3: $V(\pi,0,y)=0$ and
--   $$V(\pi,T+1,y)=\sum_a\mathbb P[\pi(T+1,y)=a]\Big(\bar\mu_a(y_a)+\mathbb E_{r\sim\text{pred}_a(y_a)}\big[V(\pi,T,y\text{ with }y_a\leftarrow\mathcal U_a(y_a,r))\big]\Big).$$
--
--   **Inner problem at time 1.** For a payoff rule on action sequences $a_{1:T}$, $Q_1(a)$ is the largest total payoff of a sequence whose first action is $a$. The three payoffs are $\mu_{a_t}$ (TS, (28)), $\hat\mu_{a_t,T-1}$ (IRS.FH, (32)) and $\hat\mu_{a_t,n_{t-1}(a_t)}$ (IRS.V-Zero, (36)), where $n_{t-1}(a)$ counts the earlier pulls of $a$. The file also defines the pull counts $N_{t-1}(a)$ and $N_T(a)$ of an action sequence.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Arms are `Fin K` and reward indices are 0-based. Every parameter space is $\Theta_a=\mathbb R$ (the reading of §2.2 that the proof of Lemma 5 needs). $W^{\rm IRS.FH}$ is defined by its closed form (33), not derived from the penalty (24). $V$ is the tower-property form of (7) for belief-Markov policies, which all three policies are (pp. 12, 14). Products of probability measures are `Measure.infinitePi`. $\max_a$ is a finite `sup'`, and the allocation set is `Finset.Nat.antidiagonalTuple K T`.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 4–20, (1)–(14), (28)–(29), (32)–(33), (36)–(37), Algorithms 1–4; p. 63, (181)–(184)

import Mathlib

namespace InfoRelaxTS.Gap

open MeasureTheory ProbabilityTheory

/-! Bayesian multi-armed bandit with natural-exponential-family rewards and conjugate priors
(Min, Maglaras, Moallemi, arXiv:1902.04251v2, §2.1–§2.2, §2.4, §3.1–§3.3, pp. 4–20).
Arms are `Fin K`, 0-based: the paper's arm `a` is index `a - 1`. Rewards of arm `a` are a
sequence `ℕ → ℝ`, 0-based: the paper's `R_{a,n}` is index `n - 1`. Every parameter space is
`Θ_a = ℝ`. A belief (hyperparameter) of one arm is `(ξ, ν) : ℝ × ℝ`. -/

/-- The natural-exponential-family data of a `K`-armed instance (11): for each arm a reference
measure `h a` on `ℝ` and a log-partition function `A a : ℝ → ℝ`. -/
structure NEFModel (K : ℕ) where
  h : Fin K → Measure ℝ
  A : Fin K → ℝ → ℝ

variable {K : ℕ}

/-- `A a` is the logarithm of the normalization factor of (11):
`∫ e^{θ r} h_a(dr) = e^{A_a(θ)}` for every arm and every `θ ∈ ℝ`. -/
def IsNormalized (M : NEFModel K) : Prop :=
  ∀ a θ, ∫⁻ r, ENNReal.ofReal (Real.exp (θ * r)) ∂(M.h a) = ENNReal.ofReal (Real.exp (M.A a θ))

/-- `L`-smoothness (59) of every log-partition function: `A_a` is `C²` and `A_a'' ≤ L` on `ℝ`. -/
def IsLSmooth (M : NEFModel K) (L : ℝ) : Prop :=
  ∀ a, ContDiff ℝ 2 (M.A a) ∧ ∀ θ, deriv (deriv (M.A a)) θ ≤ L

/-- Reward law (11): `ℙ[R_{a,n} ∈ dr | θ_a] = h_a(dr) exp(θ_a r − A_a(θ_a))`. -/
noncomputable def rewardLaw (M : NEFModel K) (a : Fin K) (θ : ℝ) : Measure ℝ :=
  (M.h a).withDensity fun r => ENNReal.ofReal (Real.exp (θ * r - M.A a θ))

/-- The inverse normalization factor `1 / f_a(ξ, ν) = ∫ exp(ξ θ − ν A_a(θ)) dθ` of (12). -/
noncomputable def priorMass (M : NEFModel K) (a : Fin K) (yb : ℝ × ℝ) : ℝ :=
  ∫ θ, Real.exp (yb.1 * θ - yb.2 * M.A a θ)

/-- Conjugate prior (12): `ℙ_{(ξ,ν)}[θ_a ∈ dθ] = f_a(ξ, ν) exp(ξ θ − ν A_a(θ)) dθ`. -/
noncomputable def prior (M : NEFModel K) (a : Fin K) (yb : ℝ × ℝ) : Measure ℝ :=
  volume.withDensity fun θ =>
    ENNReal.ofReal (Real.exp (yb.1 * θ - yb.2 * M.A a θ) / priorMass M a yb)

/-- The prior (12) at `(ξ, ν)` is proper: `ν > 0` and the density is integrable. -/
def IsProperPrior (M : NEFModel K) (a : Fin K) (yb : ℝ × ℝ) : Prop :=
  0 < yb.2 ∧ Integrable (fun θ => Real.exp (yb.1 * θ - yb.2 * M.A a θ))

/-- Bayesian update (13): `𝒰_a((ξ, ν), r) = (ξ + r, ν + 1)`. -/
def U (yb : ℝ × ℝ) (r : ℝ) : ℝ × ℝ := (yb.1 + r, yb.2 + 1)

/-- Predictive law of the next reward of arm `a` under belief `yb`: `θ ∼ 𝒫_a(yb)`, then
`r ∼ 𝓡_a(θ)`. -/
noncomputable def predLaw (M : NEFModel K) (a : Fin K) (yb : ℝ × ℝ) : Measure ℝ :=
  (prior M a yb).bind (rewardLaw M a)

/-- Conditional mean reward (9): `μ_a(θ) = 𝔼[R_{a,n} | θ_a = θ]`. -/
noncomputable def mu (M : NEFModel K) (a : Fin K) (θ : ℝ) : ℝ :=
  ∫ r, r ∂(rewardLaw M a θ)

/-- Predictive mean reward (9): `μ̄_a(ξ, ν) = 𝔼_{(ξ,ν)}[μ_a(θ_a)]`. -/
noncomputable def muBar (M : NEFModel K) (a : Fin K) (yb : ℝ × ℝ) : ℝ :=
  ∫ θ, mu M a θ ∂(prior M a yb)

/-- Outcomes (4): for each arm, its parameter and its reward sequence. -/
abbrev Outcome (K : ℕ) : Type := Fin K → ℝ × (ℕ → ℝ)

/-- Law of one arm's outcome: `θ_a ∼ 𝒫_a(y_a)`, then i.i.d. rewards `R_{a,n} ∼ 𝓡_a(θ_a)` (1)–(2). -/
noncomputable def armLaw (M : NEFModel K) (a : Fin K) (yb : ℝ × ℝ) : Measure (ℝ × (ℕ → ℝ)) :=
  (prior M a yb).bind fun θ =>
    (Measure.dirac θ).prod (Measure.infinitePi fun _ : ℕ => rewardLaw M a θ)

/-- Outcome law `ℐ(y)` (4): arms independent. -/
noncomputable def I (M : NEFModel K) (y : Fin K → ℝ × ℝ) : Measure (Outcome K) :=
  Measure.infinitePi fun a => armLaw M a (y a)

/-- Joint prior `𝒫(y)` of the parameter vector `θ`, arms independent. -/
noncomputable def priorLaw (M : NEFModel K) (y : Fin K → ℝ × ℝ) : Measure (Fin K → ℝ) :=
  Measure.infinitePi fun a => prior M a (y a)

/-- Posterior predictive mean (10) via the conjugate update (13): the predictive mean under the
belief `(ξ_a + R_{a,1} + ⋯ + R_{a,n}, ν_a + n)` reached after the first `n` rewards of arm `a`. -/
noncomputable def muHat (M : NEFModel K) (y : Fin K → ℝ × ℝ) (a : Fin K) (n : ℕ)
    (ω : Outcome K) : ℝ :=
  muBar M a ((y a).1 + ∑ i ∈ Finset.range n, (ω a).2 i, (y a).2 + n)

/-- `max_{a ∈ 𝒜} f(a)`. -/
noncomputable def maxArm [NeZero K] (f : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- Feasible allocations `𝒩_T = {n ∈ ℕ₀^K : Σ_a n_a = T}` (37). -/
def allocSet (K T : ℕ) : Finset (Fin K → ℕ) := Finset.Nat.antidiagonalTuple K T

theorem allocSet_nonempty [NeZero K] (T : ℕ) : (allocSet K T).Nonempty :=
  ⟨Pi.single 0 T, by simp [allocSet, Finset.Nat.mem_antidiagonalTuple]⟩

/-- Payoff `Σ_a S_{a,n_a} = Σ_a Σ_{i=0}^{n_a - 1} m_{a,i}` of an allocation (37). -/
def allocPayoff (m : Fin K → ℕ → ℝ) (n : Fin K → ℕ) : ℝ :=
  ∑ a, ∑ i ∈ Finset.range (n a), m a i

/-- Performance bound of TS (29): `W^TS(T, y) = 𝔼_y[T × max_a μ_a(θ_a)]`. -/
noncomputable def WTS [NeZero K] (M : NEFModel K) (T : ℕ) (y : Fin K → ℝ × ℝ) : ℝ :=
  T * ∫ θ, maxArm (fun a => mu M a (θ a)) ∂(priorLaw M y)

/-- Performance bound of IRS.FH, defined by its closed form (33):
`W^{IRS.FH}(T, y) = 𝔼_y[T × max_a μ̂_{a,T−1}]`. -/
noncomputable def WFH [NeZero K] (M : NEFModel K) (T : ℕ) (y : Fin K → ℝ × ℝ) : ℝ :=
  T * ∫ ω, maxArm (fun a => muHat M y a (T - 1) ω) ∂(I M y)

/-- Performance bound of IRS.V-Zero (37), (153):
`W^{IRS.V-Zero}(T, y) = 𝔼_y[max_{n ∈ 𝒩_T} Σ_a S_{a,n_a}]`. -/
noncomputable def WVZ [NeZero K] (M : NEFModel K) (T : ℕ) (y : Fin K → ℝ × ℝ) : ℝ :=
  ∫ ω, (allocSet K T).sup' (allocSet_nonempty T)
    (fun n => allocPayoff (fun a i => muHat M y a i ω) n) ∂(I M y)

/-- `sel` is an argmax selector (an arbitrary tie-breaking rule). -/
def IsArgmaxSel (sel : (Fin K → ℝ) → Fin K) : Prop :=
  ∀ (f : Fin K → ℝ) (a : Fin K), f a ≤ f (sel f)

/-- `asel T m` is an optimal allocation of the IRS.V-Zero inner problem (37) for the payoff
array `m a i = μ̂_{a,i}` (an arbitrary tie-breaking rule). -/
def IsOptAllocSel (asel : ℕ → (Fin K → ℕ → ℝ) → (Fin K → ℕ)) : Prop :=
  ∀ T m, asel T m ∈ allocSet K T ∧ ∀ n ∈ allocSet K T, allocPayoff m n ≤ allocPayoff m (asel T m)

/-- A belief-Markov randomized policy: remaining horizon and current belief ↦ law of the action. -/
abbrev Policy (K : ℕ) : Type := ℕ → (Fin K → ℝ × ℝ) → Measure (Fin K)

/-- Thompson sampling (Algorithm 2): sample `θ̃ ∼ 𝒫(y)`, play `argmax_a μ_a(θ̃_a)`. -/
noncomputable def tsPol (M : NEFModel K) (sel : (Fin K → ℝ) → Fin K) : Policy K :=
  fun _T y => (priorLaw M y).map fun θ => sel fun a => mu M a (θ a)

/-- IRS.FH (Algorithm 4): sample `ω̃ ∼ ℐ(y)`, play `argmax_a μ̂_{a,T−1}(ω̃)`. -/
noncomputable def fhPol (M : NEFModel K) (sel : (Fin K → ℝ) → Fin K) : Policy K :=
  fun T y => (I M y).map fun ω => sel fun a => muHat M y a (T - 1) ω

/-- IRS.V-Zero (§3.3): sample `ω̃ ∼ ℐ(y)`, solve (37) for an optimal allocation `ñ*`, play
`argmax_a ñ*_a`. -/
noncomputable def vzPol (M : NEFModel K) (asel : ℕ → (Fin K → ℕ → ℝ) → (Fin K → ℕ))
    (sel : (Fin K → ℝ) → Fin K) : Policy K :=
  fun T y => (I M y).map fun ω => sel fun a => ((asel T (fun b i => muHat M y b i ω) a : ℕ) : ℝ)

/-- Bayesian performance (7) of a belief-Markov policy, in the recursive form of the outer loop
(Algorithms 1 and 3): at remaining horizon `T + 1` and belief `y`, draw `a ∼ p(T + 1, y)`, earn
`μ̄_a(y_a)` in expectation, observe `r` from the predictive law of arm `a`, and continue from the
updated belief. -/
noncomputable def V (M : NEFModel K) (p : Policy K) : ℕ → (Fin K → ℝ × ℝ) → ℝ
  | 0, _ => 0
  | T + 1, y => ∑ a, (p (T + 1) y {a}).toReal *
      (muBar M a (y a) + ∫ r, V M p T (Function.update y a (U (y a) r)) ∂(predLaw M a (y a)))

/-- Number of pulls of arm `a` before time `t` in the action sequence `s` (the paper's
`n_{t−1}(a_{1:t−1}, a)`, with `t` 0-based). -/
def pullsBefore {T : ℕ} (s : Fin T → Fin K) (t : Fin T) (a : Fin K) : ℕ :=
  (Finset.univ.filter fun t' : Fin T => t' < t ∧ s t' = a).card

/-- Total number of pulls `N_T(a) = n_T(a_{1:T}, a)` of arm `a` in `s`. -/
def pullCount {T : ℕ} (s : Fin T → Fin K) (a : Fin K) : ℕ :=
  (Finset.univ.filter fun t : Fin T => s t = a).card

/-- Time-1 value `Q_1^{z,in}(a)` of the deterministic inner problem: the best total penalized
payoff over action sequences `s : Fin T → Fin K` whose first action is `a`
((181)–(182) unrolled; the condition is void when `T = 0`). -/
noncomputable def Q1 {T : ℕ} (pay : (Fin T → Fin K) → Fin T → ℝ) (a : Fin K) : ℝ :=
  (Finset.univ.filter fun s : Fin T → Fin K => ∀ t : Fin T, t.val = 0 → s t = a).sup'
    ⟨fun _ => a, by simp⟩ (fun s => ∑ t, pay s t)

/-- Penalized payoff of `z^TS` (28): `μ_{a_t}(θ_{a_t})`. -/
def payTS {T : ℕ} (μv : Fin K → ℝ) : (Fin T → Fin K) → Fin T → ℝ :=
  fun s t => μv (s t)

/-- Penalized payoff of `z^{IRS.FH}` (32): `μ̂_{a_t, T−1}`. -/
def payFH {T : ℕ} (m : Fin K → ℕ → ℝ) : (Fin T → Fin K) → Fin T → ℝ :=
  fun s t => m (s t) (T - 1)

/-- Penalized payoff of `z^{IRS.V-Zero}` (36): `μ̂_{a_t, n_{t−1}(a_t)}`. -/
def payVZ {T : ℕ} (m : Fin K → ℕ → ℝ) : (Fin T → Fin K) → Fin T → ℝ :=
  fun s t => m (s t) (pullsBefore s t (s t))

end InfoRelaxTS.Gap


