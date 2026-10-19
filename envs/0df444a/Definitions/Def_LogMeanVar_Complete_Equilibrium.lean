-- Prove2me | Definitions.Def_LogMeanVar_Complete_Equilibrium
-- name    : LogMeanVar_Complete_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:57.490881+00:00
-- url     : https://prove2.me/theorems/5c3e4c6a-ecad-47ff-884a-9c4f7d8c4f56
-- title:
--   J of p. 8, the perturbation π^{h,v} and Definition 1, p. 9 — equilibrium strategies for the log-return mean-variance criterion
-- statement:
--   This file defines the reward function of p. 8, the perturbation strategies and the equilibrium notion of Definition 1 (p. 9).
--
--   For a strategy $\pi$, a time $t$ and a starting log-wealth $y$, let $R^\pi$ be a solution of the log-return equation (6) started at $R_t=y$. The **reward function** is
--   $$J(t,y;\pi)=\mathbb E_t\big[R^\pi_T\big]-\frac\gamma2\,\mathrm{Var}_t\big[R^\pi_T\big],$$
--   the mean minus $\gamma/2$ times the variance of the terminal log-wealth of the process started at $(t,y)$.
--
--   Given a strategy $\hat\pi$, a time $t$, $h>0$ and $v\in\mathbb R$, the **perturbation** $\pi^{h,v}$ is
--   $$\pi^{h,v}(\tau,y)=\begin{cases}v,& t\le\tau<t+h,\\ \hat\pi(\tau,y),&\text{otherwise (in particular } t+h\le\tau\le T).\end{cases}$$
--
--   An admissible strategy $\hat\pi$ is an **equilibrium strategy** if for every $t\in[0,T)$, every $y\in\mathbb R$ and every $v\in\mathbb R$ for which the perturbations $\pi^{h,v}$ are admissible (for all small $h>0$),
--   $$\liminf_{h\to0^+}\frac{J(t,y;\hat\pi)-J(t,y;\pi^{h,v})}{h}\ \ge\ 0 .$$
--   In words: deviating to a constant fraction on a short interval and then returning to $\hat\pi$ cannot improve the criterion to first order.
--
--   **Formalization Note** $\mathbb E_t$, $\mathrm{Var}_t$ are read as the moments of the process started at $(t,y)$ (the Markovian reading of Björk, Khapko and Murgoci, used by the paper's restriction to feedback strategies). $J$ evaluates one chosen solution (`Classical.epsilon`); for admissible strategies all solutions agree almost surely, so the value does not depend on the choice. The $\liminf\ge0$ is written in $\varepsilon$-form: for every $\varepsilon>0$, eventually as $h\to0^+$ the quotient is $\ge-\varepsilon$, which is $\liminf\ge0$ in the extended reals. The time index $t$ of $\mathcal A_t$ is read into "$\pi^{h,v}\in\mathcal A$".
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. 8, (7) and J; p. 9, Definition 1

import Mathlib
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The reward function of p. 8, `J(t, y; π) = E_t[R^π_T] - (γ/2) Var_t[R^π_T]`, computed on a
solution `R^π` of (6) started at `R_t = y` (any solution; under `Admissible` all solutions agree
a.s. on `[t, T]`, so the value does not depend on the choice).

**Formalization Note** `E_t`, `Var_t` are read as the mean and variance of the process started
at `(t, y)` (the Markovian reading, as in Björk–Khapko–Murgoci); `γ` is the constant of
Assumption A. -/
noncomputable def J (M : Market) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (t y : ℝ) : ℝ :=
  let R := Classical.epsilon (fun R => IsLogReturn M P B π t y R)
  (∫ ω, R M.T ω ∂P) - M.γ / 2 * variance (R M.T) P

open Classical in
/-- The perturbation strategy `π^{h,v}` of Definition 1, p. 9: `v` for `t ≤ τ < t + h` and
`π̂(τ, y)` otherwise (in particular for `t + h ≤ τ ≤ T`). Defined for every `h`. -/
noncomputable def spike (πh : Strategy) (t h v : ℝ) : Strategy :=
  fun τ y => if τ ∈ Ico t (t + h) then v else πh τ y

/-- Definition 1, p. 9: an admissible strategy `π̂` is an equilibrium strategy for problem (7)
if at any time `t ∈ [0, T)`, for every starting log-wealth `y` and every `v ∈ ℝ` such that the
perturbation `π^{h,v}` is admissible (for all small `h > 0`),
`liminf_{h → 0+} [J(t, y; π̂) - J(t, y; π^{h,v})]/h ≥ 0`.

**Formalization Note** The `liminf ≥ 0` is written in `ε`-form (for every `ε > 0`, eventually
as `h → 0+`, the quotient is `≥ -ε`), which is `liminf ≥ 0` in the extended reals. -/
def IsEquilibrium (M : Market) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (πh : Strategy) : Prop :=
  Admissible M P B πh ∧
  ∀ t ∈ Ico 0 M.T, ∀ y v : ℝ,
    (∀ᶠ h in 𝓝[>] (0 : ℝ), Admissible M P B (spike πh t h v)) →
    ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      -ε ≤ (J M P B πh t y - J M P B (spike πh t h v) t y) / h

end LogMeanVar.Complete


