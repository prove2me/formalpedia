-- Prove2me | Definitions.Def_PoissonDepTrials_SecondOrder_Setting
-- name    : PoissonDepTrials_SecondOrder_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:23:52.614525+00:00
-- url     : https://prove2.me/theorems/4024427b-c02d-4e5a-92fe-992674c66927
-- title:
--   §2, §5, pp. 535–545 — Bernoulli trials, p_i, λ, W, W^{(i)}, λ^{(i)}, 𝒫_λ (2.4), the Stein solution S_λh (2.5), Δ, and the operators L and U_λ
-- statement:
--   This file fixes the objects of Chen's second-order Poisson expansion for sums of Bernoulli trials.
--
--   1. **Trials.** On a probability space $(\Omega,\mathcal F,P)$, random variables $X_1,\dots,X_n$ are *Bernoulli trials* when each $X_i$ is measurable and takes the values $0$ and $1$ only (almost surely). Following the paper, $X_i$ is taken to be identically $0$ for $i\le 0$ and $i\ge n+1$.
--   2. **Success probabilities and sums.** $p_i=P(X_i=1)$, $\lambda=\sum_{i=1}^n p_i$, $W=\sum_{i=1}^n X_i$, $W^{(i)}=\sum_{k\ne i}X_k$, and $\lambda^{(i)}=\sum_{j\ne i}p_j$ (indices in $\{1,\dots,n\}$).
--   3. **Poisson expectation** (2.4). For a function $h$ on the nonnegative integers,
--   $$\mathscr P_\lambda h=e^{-\lambda}\sum_{k=0}^\infty h(k)\frac{\lambda^k}{k!}.$$
--   4. **Stein solution** (2.5). For $w\ge1$,
--   $$S_\lambda h(w)=-(w-1)!\,\lambda^{-w}\sum_{k=0}^{w-1}\bigl[h(k)-\mathscr P_\lambda h\bigr]\frac{\lambda^k}{k!},$$
--   the solution of the Stein equation $wf(w)-\lambda f(w+1)=h(w)-\mathscr P_\lambda h$ for $w\ge1$.
--   5. **Operators.** $\Delta f(w)=f(w+1)-f(w)$, $Lf(w)=f(w+1)$, and $U_\lambda h(w)=\Delta S_\lambda h(w+1)$ for $w\ge0$ (§5, p. 543).
--
--   These are the objects in which Chen's refinement (Theorem 5.1) is stated: the second-order correction to $Eh(W)\approx\mathscr P_\lambda h$ is $-(\sum_i p_i^2)\mathscr P_\lambda U_\lambda h$.
--
--   **Formalization Note** $p_i$ is defined from $X$ (not a free parameter). $S_\lambda h(0)$ evaluates to $0$ (an empty sum) and plays no role: the page defines $S_\lambda h$ only for $w\ge1$, and $U_\lambda h$ only evaluates it at arguments $\ge1$. $\mathscr P_\lambda h$ is a `tsum`, which is a genuine sum whenever $h$ is bounded, as in every statement of this mission.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 535–536, §2, (2.3)–(2.5); p. 543, §5 (operators L, U_λ); p. 545 (λ^{(i)})

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.SecondOrder

/-- Chen (1975), §2, p. 535: `X 1, …, X n` are Bernoulli random variables (values in `{0, 1}`
almost surely), and, following the convention of p. 535, `X i` is identically zero when `i ≤ 0`
or `i ≥ n + 1`. Each `X i` is measurable. -/
def IsBernoulliTrials {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) : Prop :=
  (∀ i, Measurable (X i)) ∧ (∀ i, (i = 0 ∨ n < i) → X i = 0) ∧ ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1

/-- `p_i = P(X_i = 1)` (§2, p. 535). -/
noncomputable def prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ)
    (i : ℕ) : ℝ :=
  P.real {ω | X i ω = 1}

/-- `λ = Σ_{i=1}^n p_i` (§2, p. 535). -/
noncomputable def lam {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, prob P X i

/-- `λ^{(i)} = Σ_{j ≠ i} p_j` (proof of Theorem 5.1, p. 545). -/
noncomputable def lamExcept {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) (i : ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i), prob P X j

/-- `W = Σ_{i=1}^n X_i` (§2, p. 535). -/
def W {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω => ∑ i ∈ Finset.Icc 1 n, X i ω

/-- `W^{(i)} = Σ_{k ≠ i} X_k` (§2, p. 535). -/
def Wi {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) : Ω → ℕ :=
  fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), X k ω

/-- The Poisson expectation `𝒫_λh = e^{−λ} Σ_{k≥0} h(k) λ^k / k!` (2.4), p. 536. -/
noncomputable def poissonExp (lam : ℝ) (h : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * h k

/-- The solution `S_λh(w)` of the Stein equation (2.3), given for `w ≥ 1` by the first line of
(2.5), p. 536: `−(w − 1)! λ^{−w} Σ_{k=0}^{w−1} [h(k) − 𝒫_λh] λ^k / k!`. Its value at `w = 0`
(an empty sum, `0`) plays no role. -/
noncomputable def stein (lam : ℝ) (h : ℕ → ℝ) (w : ℕ) : ℝ :=
  -(((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
    ∑ k ∈ Finset.range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ))

/-- The forward difference `Δf(w) = f(w + 1) − f(w)` (p. 536). -/
def delta (f : ℕ → ℝ) (w : ℕ) : ℝ := f (w + 1) - f w

/-- The shift operator `Lf(w) = f(w + 1)` (§5, p. 543). -/
def shiftL (f : ℕ → ℝ) : ℕ → ℝ := fun w => f (w + 1)

/-- The operator `U_λh(w) = ΔS_λh(w + 1)` (§5, p. 543), defined for every `w ≥ 0`. -/
noncomputable def stU (lam : ℝ) (h : ℕ → ℝ) : ℕ → ℝ :=
  fun w => delta (stein lam h) (w + 1)

end PoissonDepTrials.SecondOrder


