-- Prove2me | Definitions.Def_SwitchbackExp_Design_Model
-- name    : SwitchbackExp_Design_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:28:38.783915+00:00
-- url     : https://prove2.me/theorems/b707b419-00e9-403c-b47d-2b0e92620597
-- title:
--   §2, pp. 5–11 — assignment paths, potential outcomes, Assumptions 1–3, regular switchback designs (3), the Horvitz–Thompson estimator (4) and the risk (5)
-- statement:
--   This file sets up the potential-outcomes model of a switchback experiment on a single experimental unit observed over periods $t\in[T]=\{1,\dots,T\}$.
--
--   **Paths and potential outcomes.** An assignment path is $w_{1:T}\in\{0,1\}^T$, where $w_t=1$ means treatment and $w_t=0$ control. For every period $t$ and every path there is a potential outcome $Y_t(w_{1:T})\in\mathbb R$; the collection is $\mathbb Y=\{Y_t(w_{1:T})\}$.
--
--   **Assumptions.**
--   1. *Non-anticipating outcomes* (Assumption 1): $Y_t(w_{1:T})$ depends on $w$ only through $w_{1:t}$.
--   2. *$m$-carryover effects* (Assumption 2): for $t\in\{m+1,\dots,T\}$, $Y_t(w_{1:T})$ does not depend on $w_{1:t-m-1}$.
--   3. *Bounded outcomes* (Assumption 3): $|Y_t(w)|\le B$ for all $t\in[T]$ and all paths $w$.
--
--   Under Assumptions 1–2, $Y_t(\mathbf 1_{m+1})$ and $Y_t(\mathbf 0_{m+1})$ denote the outcome at $t$ after $m+1$ consecutive treatments, respectively controls.
--
--   **Regular designs.** Randomization points $\mathbb T=\{t_0=1<t_1<\dots<t_K\}\subseteq[T]$ with $K\ge1$, and probabilities $\mathbb Q=(q_0,\dots,q_K)\in(0,1)^{K+1}$, define the regular switchback experiment $(\mathbb T,\mathbb Q)$: an independent coin with success probability $q_k$ is flipped at $t_k$, and its outcome is the assignment of every period $t_k\le t\le t_{k+1}-1$ (with $t_{K+1}=T+1$). Its law $\eta_{\mathbb T,\mathbb Q}$ on paths is display (3):
--   $$\eta_{\mathbb T,\mathbb Q}(w_{1:T})=\prod_{k=0}^K q_{t_k}^{\mathbf 1\{w_{t_k}=1\}}\,\bar q_{t_k}^{\mathbf 1\{w_{t_k}=0\}}$$
--   if $w$ is constant on every block $\{t_k,\dots,t_{k+1}-1\}$, and $0$ otherwise, where $\bar q=1-q$. The determining randomization point of period $t$ is $f_{\mathbb T}(t)=\max\{j\in\mathbb T: j\le t\}$.
--
--   **Estimand, estimator, risk.** The lag-$m$ causal effect of consecutive treatments (display (1) with $p=m$) is
--   $$\tau_m(\mathbb Y)=\frac1{T-m}\sum_{t=m+1}^T\bigl[Y_t(\mathbf 1_{m+1})-Y_t(\mathbf 0_{m+1})\bigr].$$
--   For a realized path $w$, the Horvitz–Thompson estimator (4) is
--   $$\hat\tau_m(w)=\frac1{T-m}\sum_{t=m+1}^T\Bigl[\frac{Y_t(w)\,\mathbf 1\{w_{t-m:t}=\mathbf 1_{m+1}\}}{\Pr(W_{t-m:t}=\mathbf 1_{m+1})}-\frac{Y_t(w)\,\mathbf 1\{w_{t-m:t}=\mathbf 0_{m+1}\}}{\Pr(W_{t-m:t}=\mathbf 0_{m+1})}\Bigr],$$
--   with probabilities under $\eta_{\mathbb T,\mathbb Q}$, and the risk (5) is $r(\eta_{\mathbb T,\mathbb Q},\mathbb Y)=\mathbb E_{W\sim\eta_{\mathbb T,\mathbb Q}}\bigl[(\hat\tau_m(W)-\tau_m(\mathbb Y))^2\bigr]$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** A path is a function $\mathbb N\to\{\text{true},\text{false}\}$ of which only the indices $1,\dots,T$ are read; potential outcomes are a function of the period and the whole path, and Assumptions 1–3 are separate predicates. $Y_t(\mathbf 1_{m+1})$ and $Y_t(\mathbf 0_{m+1})$ are the outcomes on the all-treatment and all-control paths, which under Assumptions 1–2 coincide with every path whose window $w_{t-m:t}$ is constant. The point set is a `Finset ℕ` and $q$ is indexed by the randomization point itself ($q_{t_k}$, as in (3)). The expectation under (3) is a finite sum over the $2^{K+1}$ coin vectors of the image path times the product of the coin probabilities: the map from coin vectors to paths is a bijection onto the support of $\eta_{\mathbb T,\mathbb Q}$, so this is the expectation under (3) for every function of $w_{1:T}$. Divisions use Lean's convention $x/0=0$; every theorem that evaluates the estimator assumes $q\in(0,1)$, which makes the denominators positive.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), §2, pp. 5–11, Assumptions 1–3, Definition 1, (1)–(5); f_𝕋 from EC.3.1, p. ec3

import Mathlib

namespace SwitchbackExp.Design

open Finset

/-- An assignment path `w_{1:T}` (§2.1, p. 5): `w t = true` iff `W_t = 1` (treatment). Only `1 ≤ t ≤ T` is read. -/
abbrev Path := ℕ → Bool

/-- Potential outcomes (§2.1, p. 5): `Y t w = Y_t(w_{1:T})`. -/
abbrev Outcomes := ℕ → Path → ℝ

/-- Assumption 1 (Non-anticipating Potential Outcomes, p. 6): `Y_t` depends on `w` only through `w_{1:t}`. -/
def NonAnticipating (T : ℕ) (Y : Outcomes) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ w w' : Path, (∀ s, 1 ≤ s → s ≤ t → w s = w' s) → Y t w = Y t w'

/-- Assumption 2 (m-Carryover Effects, p. 6): for `t ∈ {m+1, …, T}`, `Y_t` does not depend on `w_{1:t−m−1}`. -/
def Carryover (m T : ℕ) (Y : Outcomes) : Prop :=
  ∀ t, m + 1 ≤ t → t ≤ T → ∀ w w' : Path, (∀ s, t - m ≤ s → s ≤ T → w s = w' s) → Y t w = Y t w'

/-- Assumption 3 (Bounded Potential Outcomes, p. 12): `|Y_t(w)| ≤ B` for all `t ∈ [T]` and all paths. -/
def Bounded (B : ℝ) (T : ℕ) (Y : Outcomes) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ w : Path, |Y t w| ≤ B

/-- `Y_t(1_{m+1})` (p. 7): the outcome under consecutive treatments. -/
def Y1 (Y : Outcomes) (t : ℕ) : ℝ := Y t (fun _ => true)

/-- `Y_t(0_{m+1})` (p. 7): the outcome under consecutive controls. -/
def Y0 (Y : Outcomes) (t : ℕ) : ℝ := Y t (fun _ => false)

/-- The randomization points `𝕋 = {t₀ = 1 < t₁ < … < t_K} ⊆ [T]` with `K` a positive integer (§2.3, p. 8). -/
def IsRegularPoints (T : ℕ) (P : Finset ℕ) : Prop :=
  1 ∈ P ∧ P ⊆ Finset.Icc 1 T ∧ 2 ≤ P.card

/-- The randomization probabilities `ℚ ∈ (0,1)^{K+1}` (p. 8), indexed by the randomization point:
`q t_k` is the paper's `q_k` (the paper itself writes `q_{t_k}` in (3)). -/
def IsRegularProbs (P : Finset ℕ) (q : ℕ → ℝ) : Prop :=
  ∀ t ∈ P, 0 < q t ∧ q t < 1

/-- `f_𝕋(t) = max{j ∈ 𝕋 : j ≤ t}` (EC.3.1, p. ec3), the determining randomization point of period `t`. -/
def detPoint (P : Finset ℕ) (t : ℕ) : ℕ := (P.filter (· ≤ t)).sup id

/-- The path a coin vector produces (Definition 1, (2)): `W_t` is the coin flipped at `f_𝕋(t)`. -/
def pathOf (P : Finset ℕ) (c : P → Bool) : Path := fun t =>
  if h : detPoint P t ∈ P then c ⟨detPoint P t, h⟩ else false

/-- The probability of a coin vector: `∏_k q_k^{1{c_k = 1}} (1 − q_k)^{1{c_k = 0}}`, the nonzero values of (3). -/
noncomputable def coinProb (P : Finset ℕ) (q : ℕ → ℝ) (c : P → Bool) : ℝ :=
  ∏ p : P, if c p then q p else 1 - q p

/-- `E_{W ∼ η_{𝕋,ℚ}}[g(W)]` (p. 10): the expectation under the law (3) of the regular design `(𝕋, ℚ)`. -/
noncomputable def expect (P : Finset ℕ) (q : ℕ → ℝ) (g : Path → ℝ) : ℝ :=
  ∑ c : P → Bool, coinProb P q c * g (pathOf P c)

/-- `1{w_{t−m:t} = 1_{m+1}}`. -/
def onesInd (m : ℕ) (w : Path) (t : ℕ) : ℝ :=
  if ∀ s ∈ Finset.Icc (t - m) t, w s = true then 1 else 0

/-- `1{w_{t−m:t} = 0_{m+1}}`. -/
def zerosInd (m : ℕ) (w : Path) (t : ℕ) : ℝ :=
  if ∀ s ∈ Finset.Icc (t - m) t, w s = false then 1 else 0

/-- The lag-m estimand `τ_m(Y)`, display (1) with `p = m` (p. 7). -/
noncomputable def tau (m T : ℕ) (Y : Outcomes) : ℝ :=
  (1 / ((T : ℝ) - m)) * ∑ t ∈ Finset.Icc (m + 1) T, (Y1 Y t - Y0 Y t)

/-- The Horvitz–Thompson estimator, display (4) with `p = m` (p. 10). The denominators are
`Pr(W_{t−m:t} = 1_{m+1})` and `Pr(W_{t−m:t} = 0_{m+1})` under `(𝕋, ℚ)`. -/
noncomputable def htEstimator (m T : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) (w : Path) : ℝ :=
  (1 / ((T : ℝ) - m)) * ∑ t ∈ Finset.Icc (m + 1) T,
    (Y t w * onesInd m w t / expect P q (fun v => onesInd m v t)
      - Y t w * zerosInd m w t / expect P q (fun v => zerosInd m v t))

/-- The risk function `r(η_{𝕋,ℚ}, 𝕐)`, display (5) (p. 11). -/
noncomputable def risk (m T : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) : ℝ :=
  expect P q (fun w => (htEstimator m T P q Y w - tau m T Y) ^ 2)

end SwitchbackExp.Design


