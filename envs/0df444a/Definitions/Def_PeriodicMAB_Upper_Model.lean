-- Prove2me | Definitions.Def_PeriodicMAB_Upper_Model
-- name    : PeriodicMAB_Upper_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:11.233478+00:00
-- url     : https://prove2.me/theorems/16beec1f-6fd5-462a-bb10-18c870051685
-- title:
--   §2, pp. 6–9, 18 — periodic means with minimum periods, Fourier coefficients, $B_k$, $b_k$, Assumptions 1–2, rewards, pseudo-regret (1)
-- statement:
--   The periodic multi-armed bandit of §2. A decision maker pulls one of $K$ arms at each epoch $t=1,\dots,T$. Pulling arm $k$ at epoch $t$ yields the reward
--
--   $$
--   Y_{k,t}=\mu_{k,t}+\epsilon_t ,
--   $$
--
--   where the mean $\mu_{k,t}$ repeats with a **minimum period** $T_k\in\mathbb N^+$: $\mu_{k,t+T_k}=\mu_{k,t}$ for all $t\ge1$, and no smaller positive shift has this property.
--
--   This file defines:
--
--   1. **Minimum period.** $p$ is the minimum period of a sequence $f$ if $p\ge1$, $f(t+p)=f(t)$ for every $t\ge1$, and no $q$ with $0<q<p$ satisfies $f(t+q)=f(t)$ for all $t\ge1$.
--   2. **Fourier coefficients** (display (2), p. 8). For a sequence of period $p$,
--   $$
--   b_{j}=\frac1p\sum_{t=1}^{p}\mu_{t}\,e^{-2\pi i jt/p},\qquad j=0,\dots,p-1,
--   $$
--   which are the unique coefficients with $\mu_t=\sum_{j=0}^{p-1}b_j e^{2\pi i jt/p}$ for $t\ge1$. The **present frequencies** are the $j/p$ with $|b_j|>0$.
--   3. $B_k=\max\{|b_{k,j}|:|b_{k,j}|>0\}$ and $b_k=\min\{|b_{k,j}|:|b_{k,j}|>0\}$ (displays (11)–(12), p. 18).
--   4. **Assumption 1** (p. 7): $\mu_{k,t}\in[0,1]$ for every arm $k$ and every $t\in\{1,\dots,T\}$.
--   5. **Assumption 2** (p. 7): the noises $\epsilon_t$ are independent and sub-Gaussian with parameter $\sigma$: $\mathbb E[e^{\lambda\epsilon_t}]\le e^{\sigma^2\lambda^2/2}$ for every real $\lambda$, and $\mathbb P(|\epsilon_t|>x)\le 2e^{-x^2/(2\sigma^2)}$ for every $x>0$.
--   6. The **pseudo-regret** (display (1), p. 7) of an arm sequence $\pi$:
--   $$
--   R^\pi_T=\sum_{t=1}^{T}\Big(\max_{k}\mu_{k,t}-\mu_{\pi_t,t}\Big),
--   $$
--   and the number of effective arms $d=\sum_{k=1}^K T_k$ (p. 14).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Epochs are natural numbers $t\ge1$; the value of a mean sequence at $t=0$ is never read. Arms are `Fin K`, so the paper's arm $k$ is index $k-1$. $B_k$ and $b_k$ take the value $0$ when no coefficient is present (which happens only if the means vanish on a whole period); Assumption 4 rules this case out. The sub-Gaussian MGF bound is Mathlib's `HasSubgaussianMGF` with variance proxy $\sigma^2$, which includes integrability of $e^{\lambda\epsilon_t}$; the printed tail bound is kept as a separate clause, although it follows from the MGF bound. Independence is required of the whole noise sequence $(\epsilon_t)_{t\in\mathbb N}$; noise after the horizon is never read. The maximum over arms is $0$ when there are no arms.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, pp. 6–9, 18, §2, Assumptions 1–2, (1), (2), (11), (12)

import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-! Chen, Wang and Wang, *Learning and Optimization with Seasonal Patterns*,
arXiv:2005.08088v4, §2 (pp. 6–7) and pp. 8–9, 18: the periodic multi-armed bandit model.

Conventions. Epochs are `1, 2, …` (natural numbers `t ≥ 1`); the value of a mean sequence
at `t = 0` is never read. Arms are `Fin K`: the paper's arm `k` is index `k - 1`. -/

/-- `p` is the **minimum period** of the sequence `f` on the epochs `t ≥ 1`:
`p ≥ 1`, `f (t + p) = f t` for every `t ≥ 1`, and no `q` with `0 < q < p` has this
property (paper, p. 7: "`µ_{k,t+T_k} = µ_{k,t}` … `T_k ∈ ℕ⁺` denotes the (minimum) period"). -/
def IsMinPeriod (f : ℕ → ℝ) (p : ℕ) : Prop :=
  0 < p ∧ (∀ t, 1 ≤ t → f (t + p) = f t) ∧
    ∀ q, 0 < q → q < p → ¬ ∀ t, 1 ≤ t → f (t + q) = f t

/-- The Fourier coefficient `b_{k,j}` of display (2), p. 8, of a sequence `μk` of period `p`:
`b_j = (1/p) ∑_{t=1}^{p} μk t · exp(−2πi j t / p)`. For a `p`-periodic sequence these are the
unique coefficients with `μk t = ∑_{j=0}^{p-1} b_j exp(2πi j t / p)` for all `t ≥ 1`. -/
noncomputable def fourierCoeff (μk : ℕ → ℝ) (p j : ℕ) : ℂ :=
  (1 / (p : ℂ)) * ∑ t ∈ Icc 1 p,
    (μk t : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (t : ℂ) / (p : ℂ)))

/-- The indices `j ∈ {0, …, p − 1}` of the **present frequencies** `j/p`, those with
`|b_{k,j}| > 0` (p. 9). -/
noncomputable def presentSet (μk : ℕ → ℝ) (p : ℕ) : Finset ℕ :=
  (range p).filter (fun j => fourierCoeff μk p j ≠ 0)

/-- `B_k` of (11), p. 18: the largest modulus of a present Fourier coefficient
(value `0` when no coefficient is present, i.e. when `μk ≡ 0` on a period). -/
noncomputable def bigB (μk : ℕ → ℝ) (p : ℕ) : ℝ :=
  if h : (presentSet μk p).Nonempty then (presentSet μk p).sup' h (fun j => ‖fourierCoeff μk p j‖)
  else 0

/-- `b_k` of (12), p. 18: the smallest modulus of a present Fourier coefficient
(value `0` when no coefficient is present). -/
noncomputable def smallB (μk : ℕ → ℝ) (p : ℕ) : ℝ :=
  if h : (presentSet μk p).Nonempty then (presentSet μk p).inf' h (fun j => ‖fourierCoeff μk p j‖)
  else 0

/-- **Assumption 1** (p. 7): every mean reward `µ_{k,t}`, `t ∈ {1, …, T}`, lies in `[0, 1]`. -/
def Assumption1 {K : ℕ} (μ : Fin K → ℕ → ℝ) (T : ℕ) : Prop :=
  ∀ k t, 1 ≤ t → t ≤ T → μ k t ∈ Set.Icc (0 : ℝ) 1

/-- **Assumption 2** (p. 7): the noises `ε t` are independent sub-Gaussian random variables
with parameter `σ`: `E[exp(λ ε_t)] ≤ exp(σ²λ²/2)` for all real `λ` (Mathlib's
`HasSubgaussianMGF` with variance proxy `σ²`, which includes integrability of `exp(λ ε_t)`),
and `P(|ε_t| > x) ≤ 2 exp(−x²/(2σ²))` for all `x > 0`. Independence is required for the
whole sequence `t ∈ ℕ` (the noise after the horizon is never read). -/
structure IsSubGaussianNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) : Prop where
  indep : iIndepFun ε P
  mgf : ∀ t, HasSubgaussianMGF (ε t) (σ ^ 2) P
  tail : ∀ t (x : ℝ), 0 < x →
    P.real {ω | x < |ε t ω|} ≤ 2 * Real.exp (-x ^ 2 / (2 * (σ : ℝ) ^ 2))

/-- The reward `Y_{k,t} = µ_{k,t} + ε_t` (p. 6) of arm `k` at epoch `t` on the sample point `ω`. -/
def reward {Ω : Type*} {K : ℕ} (μ : Fin K → ℕ → ℝ) (ε : ℕ → Ω → ℝ) (ω : Ω) (k : Fin K)
    (t : ℕ) : ℝ :=
  μ k t + ε t ω

/-- `max_{k ∈ 𝒦} µ_{k,t}` (value `0` if there are no arms). -/
noncomputable def maxMean {K : ℕ} (μ : Fin K → ℕ → ℝ) (t : ℕ) : ℝ :=
  if h : (univ : Finset (Fin K)).Nonempty then univ.sup' h (fun k => μ k t) else 0

/-- The **pseudo-regret** of display (1), p. 7, of the arm sequence `π`:
`R^π_T = ∑_{t=1}^{T} (max_k µ_{k,t} − µ_{π_t,t})`. -/
noncomputable def pseudoRegret {K : ℕ} (μ : Fin K → ℕ → ℝ) (T : ℕ) (π : ℕ → Fin K) : ℝ :=
  ∑ t ∈ Icc 1 T, (maxMean μ t - μ (π t) t)

/-- `d = ∑_k T_k` (p. 14), the number of effective arms. -/
def effArms {K : ℕ} (Tper : Fin K → ℕ) : ℕ := ∑ k, Tper k

end PeriodicMAB.Upper


