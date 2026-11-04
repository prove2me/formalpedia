-- Prove2me | Definitions.Def_AIMInventory_UnknownRho_Model
-- name    : AIMInventory_UnknownRho_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:48.813986+00:00
-- url     : https://prove2.me/theorems/cd249b58-2314-48f5-9ec9-9b567c6afd5b
-- title:
--   §2.1–2.4, §3.2: non-perishable AIM, Λ₂(T), the queues W_t(θ), Z_t(θ), the busy period J₁(θ), the hitting time K(θ,z), T̃ and K̃
-- statement:
--   This file fixes the objects of Theorem 8 of Huh and Rusmevichientong (2009), in which the Adaptive Inventory Management (AIM) algorithm is run on a non-perishable lost-sales inventory system with an arbitrary step scale $\gamma>0$.
--
--   **Model.** Demands $D_1,D_2,\dots$ are independent with a common law on $[0,\infty)$ that has finite, strictly positive mean $E[D_1]$ (the published `CappedBaseStock.DemandLaw`; the path measure is the infinite product of that law). The holding and lost-sales penalty costs are $h>0$ and $b>0$. The expected one-period cost of stocking up to $y\ge0$ is
--   $$Q(y)=h\,E[y-D_1]^+ + b\,E[D_1-y]^+ ,$$
--   which is the published `backorderCost`.
--
--   **AIM, non-perishable case.** Fix an upper bound $\bar y>0$, a scale $\gamma>0$ and an initial target $\hat y_1\in[0,\bar y]$. Set $y_1=\hat y_1$, $x_1=0$, and for $t\ge1$
--   $$\epsilon_t=\frac{\gamma\bar y}{\max\{b,h\}\sqrt t},\qquad H_t(\hat y_t)=\begin{cases}h,& D_t<\hat y_t\\ -b,& D_t\ge\hat y_t\end{cases},$$
--   $$\hat y_{t+1}=\max\{\min\{\hat y_t-\epsilon_tH_t(\hat y_t),\bar y\},0\},\quad x_{t+1}=[y_t-D_t]^+,\quad y_{t+1}=\max\{\hat y_{t+1},x_{t+1}\}.$$
--   The targets $\hat y_t$, the implemented levels $y_t$ and the on-hand stock $x_t$ are deterministic functions of $D_1,\dots,D_{t-1}$. The **excess-cost term** (8) is
--   $$\Lambda_2(T)=E\Big[\frac1T\sum_{t=1}^T\big(Q(y_t)-Q(\hat y_t)\big)\Big],$$
--   and the scale of Theorem 8 is $m=h\gamma\bar y/\max\{b,h\}$, so that $h\epsilon_t=m/\sqrt t$.
--
--   **Queues.** For a real $\theta$, the fixed-inflow waiting times are $W_1(\theta)=0$, $W_{t+1}(\theta)=[W_t(\theta)+\theta-D_t]^+$, and the decreasing-inflow waiting times are $Z_1(\theta)=0$, $Z_{t+1}(\theta)=[Z_t(\theta)+\theta/\sqrt t-D_t]^+$ ($t\ge1$). With $\tau_0=1$ and $\tau_1(\theta)=\inf\{t>1: W_t(\theta)=0\}$, the first busy period is $J_1(\theta)=\{s:1<s\le\tau_1(\theta)\}$, of length $|J_1(\theta)|=\tau_1(\theta)-1\in\{1,2,\dots\}\cup\{\infty\}$.
--
--   **Hitting time** (12). For real $\theta,z$,
--   $$K(\theta,z)=\min\Big\{t\ge0 : z+\sum_{s=1}^t(\theta-D_s)\le0\Big\},$$
--   the first time the random walk started at $z$ with increments $\theta-D_s$ enters $(-\infty,0]$; it is $+\infty$ when no such $t$ exists.
--
--   **Restart times** (proof of Theorem 8). $\tilde T=\min\{t\in\mathbb Z_+ : m/\sqrt t\le\rho'\}=\max\{1,\lceil(m/\rho')^2\rceil\}$ for $\rho'>0$, and $\tilde K=\min\{t>\tilde T: Z_t(m)=0\}$, again $+\infty$ when no such $t$ exists.
--
--   The expectations $E[K(\theta,z)]$ and $E[|J_1(\theta)|^2]$ are taken in $[0,\infty]$, and the fourth central moment is $E[(D_1-E[D_1])^4]$.
--
--   These objects are shared by every statement of the mission: the goal Theorem 8, the coupling with $Z_t(m)$, the bound on $E[\tilde K]$, Claim (14) and Lemma 9.
--
--   **Formalization Note.** The demand path is zero-based: the paper's $D_t$ is `d (t-1)`, and `aimState c d n` is the state of period $n+1$. Levels are real numbers and $Q$ is evaluated through `Real.toNNReal`; only nonnegative levels occur. $W$ and $Z$ carry a junk value $0$ at index $0$, which no statement uses. $K$, $|J_1|$ and $\tilde K$ take values in $[0,\infty]$ (`ℝ≥0∞`), with $\inf\emptyset=\infty$, and their expectations are Lebesgue integrals in $[0,\infty]$, so a divergent expectation is $\infty$ and never a junk $0$. The paper's own indexing of $W$ and $Z$ (with $W_0=Z_0=0$) is not consistent with (7) at $t=0$; the convention $W_1=Z_1=0$ is the one the proofs of Theorems 6 and 8 use. The positive-mean field of the demand law is an added standing assumption (the theorems also assume $\rho'<E[D_1]$ with $\rho'>0$, which implies it).
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, pp. 5–10, §2.1–2.2 Eqs. (1), (3)–(5), §2.3.2 Eqs. (6)–(7), §2.4 Eq. (8); p. 13, §3.2 Eq. (12) and the proof of Theorem 8 (T̃, K̃)

import Mathlib
import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace AIMInventory.UnknownRho

/-- Parameters of the non-perishable AIM rule (3)--(5), including the arbitrary
initial target in the known interval. -/
structure Parameters where
  h : ℝ
  b : ℝ
  barY : ℝ
  gamma : ℝ
  initial : ℝ
  h_pos : 0 < h
  b_pos : 0 < b
  barY_pos : 0 < barY
  gamma_pos : 0 < gamma
  initial_nonneg : 0 ≤ initial
  initial_le : initial ≤ barY

abbrev DemandPath := CappedBaseStock.DemandPath
abbrev DemandLaw := CappedBaseStock.DemandLaw

/-- Equation (1) at a real stock level; only nonnegative levels occur in AIM. -/
def Q (P : DemandLaw) (c : Parameters) (y : ℝ) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.b (Real.toNNReal y)

/-- Equation (4), for the paper's positive period numbers. -/
def stepSize (c : Parameters) (t : ℕ) : ℝ :=
  c.gamma * c.barY / (max c.b c.h * Real.sqrt (t : ℝ))

/-- Equation (5): the sign is determined by the target, not the implemented level. -/
def observedSlope (c : Parameters) (target : ℝ) (demand : ℝ≥0) : ℝ :=
  if (demand : ℝ) < target then c.h else -c.b

/-- State at period `n+1` is (target, implemented level, on-hand stock).
The demand `d n` is the paper's `D_(n+1)`. -/
def aimState (c : Parameters) (d : DemandPath) : ℕ → ℝ × ℝ × ℝ
  | 0 => (c.initial, c.initial, 0)
  | n + 1 =>
      let prior := aimState c d n
      let nextTarget := max (min (prior.1 - stepSize c (n + 1) *
        observedSlope c prior.1 (d n)) c.barY) 0
      let nextHand := max (prior.2.1 - (d n : ℝ)) 0
      (nextTarget, max nextTarget nextHand, nextHand)

/-- The paper's target `ŷ_t`, indexed from 1. -/
def aimTarget (c : Parameters) (d : DemandPath) (t : ℕ) : ℝ :=
  (aimState c d (t - 1)).1

/-- The paper's implemented order-up-to level `y_t`, indexed from 1. -/
def aimLevel (c : Parameters) (d : DemandPath) (t : ℕ) : ℝ :=
  (aimState c d (t - 1)).2.1

/-- The paper's on-hand inventory `x_t`, indexed from 1. -/
def onHand (c : Parameters) (d : DemandPath) (t : ℕ) : ℝ :=
  (aimState c d (t - 1)).2.2

/-- Equation (8), `Λ₂(T)`: the expectation of average signed cost difference. -/
def lambdaTwo (P : DemandLaw) (c : Parameters) (T : ℕ) : ℝ :=
  ∫ d, ((T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
    (Q P c (aimLevel c d t) - Q P c (aimTarget c d t)))
    ∂CappedBaseStock.demandPathLaw P

/-- The scale `m = h γ ȳ / max{b,h}` in Theorem 8. -/
def m (c : Parameters) : ℝ := c.h * c.gamma * c.barY / max c.b c.h

/-- Lindley's fixed-inflow waiting time: `W₁=0`, then
`W_(t+1)=[W_t+θ-D_t]⁺` for `t≥1`. -/
def W (d : DemandPath) (θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => if t = 0 then 0 else max (W d θ t + θ - (d (t - 1) : ℝ)) 0

/-- Decreasing-inflow waiting time: `Z₁=0`, then
`Z_(t+1)=[Z_t+θ/√t-D_t]⁺` for `t≥1`. -/
def Z (d : DemandPath) (θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => if t = 0 then 0 else
      max (Z d θ t + θ / Real.sqrt (t : ℝ) - (d (t - 1) : ℝ)) 0

/-- Equation (12): first nonpositive partial sum, including time zero. The
infimum is `∞` if no time satisfies the condition. -/
def K (d : DemandPath) (θ z : ℝ) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ n : ℕ, u = (n : ℝ≥0∞) ∧
    z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) ≤ 0}

/-- `|J₁(θ)| = τ₁-1`: first positive period count returning `W` to zero.
It is `∞` on a path with no return. -/
def firstBusyLength (d : DemandPath) (θ : ℝ) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ n : ℕ, 1 ≤ n ∧ u = (n : ℝ≥0∞) ∧ W d θ (n + 1) = 0}

/-- The paper's positive-integer threshold `T̃=⌈(m/ρ′)²⌉` in the theorem's
regime `0<ρ′<m`. The max makes the auxiliary definition total elsewhere. -/
def threshold (c : Parameters) (ρ' : ℝ) : ℕ :=
  max 1 (Nat.ceil ((m c / ρ') ^ 2))

/-- `K̃`: first return of `Z(m)` strictly after `T̃`; infinite on a
path with no such return. -/
def restartTime (c : Parameters) (ρ' : ℝ) (d : DemandPath) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ t : ℕ,
    (threshold c ρ' < t) ∧ u = (t : ℝ≥0∞) ∧ Z d (m c) t = 0}

/-- The first-stop bound's initial height, `2√2 m²/ρ′`. -/
def initialHeight (c : Parameters) (ρ' : ℝ) : ℝ :=
  2 * Real.sqrt 2 * (m c) ^ 2 / ρ'

/-- Expected squared length of the first fixed-inflow busy period. -/
def busySecondMoment (P : DemandLaw) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, (firstBusyLength d θ) ^ 2 ∂CappedBaseStock.demandPathLaw P

/-- The expected hitting time appearing in Theorem 8. -/
def expectedK (P : DemandLaw) (θ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, K d θ z ∂CappedBaseStock.demandPathLaw P

/-- The fourth central demand moment in Lemma 9. -/
def centralFourth (P : DemandLaw) : ℝ :=
  ∫ d : ℝ≥0, ((d : ℝ) - CappedBaseStock.mean P) ^ 4 ∂P.law

end AIMInventory.UnknownRho


