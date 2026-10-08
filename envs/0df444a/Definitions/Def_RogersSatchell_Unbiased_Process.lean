-- Prove2me | Definitions.Def_RogersSatchell_Unbiased_Process
-- name    : RogersSatchell_Unbiased_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:33.476632+00:00
-- url     : https://prove2.me/theorems/3520ed83-6bf8-4480-9954-01118e146a17
-- title:
--   Sections 1–2: the log-price X_t = σB_t + ct, its running maximum S_t and minimum I_t, the estimator (2), and the rates α, β
-- statement:
--   Let $B = (B_t)_{t\ge 0}$ be a real-valued process on a probability space $(\Omega,\mathcal F,P)$ (in every statement of the mission, a standard Brownian motion), and fix a drift $c\in\mathbb R$ and a volatility $\sigma$. The **log-price process** is
--   $$X_t \equiv \sigma B_t + ct,\qquad t\ge 0.$$
--   Its **running maximum** and **running minimum** up to time $t$ are
--   $$S_t \equiv \sup\{X_u : 0\le u\le t\},\qquad I_t \equiv \inf\{X_u : 0\le u\le t\}.$$
--   The **high–low–close statistic** at time $t$ is $S_t(S_t-X_t)+I_t(I_t-X_t)$; at $t=1$ it is the estimator
--   $$\hat\sigma^2 \equiv S_1(S_1-X_1)+I_1(I_1-X_1)$$
--   of display (2). For a rate $\lambda>0$ and $\sigma>0$, the constants
--   $$\alpha \equiv \frac{\sqrt{c^2+2\lambda\sigma^2}-c}{\sigma^2},\qquad \beta \equiv \frac{\sqrt{c^2+2\lambda\sigma^2}+c}{\sigma^2}$$
--   are the rates of the exponential laws of $S_T$ and $-I_T$ at an independent exponential time $T$ of rate $\lambda$ (Section 2). Note $\alpha\beta = 2\lambda/\sigma^2$.
--
--   These objects are shared by every statement of the mission: $S_t$, $I_t$ and $X_t$ are the day's high, low and close of the log-price over the trading period $[0,t]$.
--
--   **Formalization Note** Time is `ℝ≥0` (as in Mathlib's `IsBrownianReal`), coerced to `ℝ` in $ct$. $S_t$ and $I_t$ are the real `sSup`/`sInf` of the image of the interval $[0,t]$ under the path $u\mapsto X_u(\omega)$; the paper's "$u\le t$" is read as $0\le u\le t$ since time starts at $0$. For a continuous path this set is compact and nonempty, so both are attained and finite; every statement of the mission assumes every sample path of $B$ is continuous. `alpha` and `beta` divide by $\sigma^2$ and are only used under $\sigma>0$. $\lambda$ is written `lam` because `λ` is reserved in Lean.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 504 (Section 1, X_t ≡ σB_t + ct), p. 505 (S_t, I_t and Eq. (2); Section 2, α and β)

import Mathlib

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

variable {Ω : Type*}

/-- The log-price process `X_t = σ B_t + c t` (Rogers–Satchell 1991, §1, p. 504), for a driving
process `B : ℝ≥0 → Ω → ℝ` (in the statements: a standard Brownian motion), volatility `σ` and
drift `c`; time `t ≥ 0` is coerced to `ℝ`. -/
noncomputable def logPrice (σ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * B t ω + c * (t : ℝ)

/-- The running maximum `S_t = sup {X_u : u ≤ t}` (§1, p. 505), the supremum of the log-price over
the time interval `u ∈ [0, t]`. For a continuous path the set is compact and nonempty, so the
supremum is a finite, attained maximum. -/
noncomputable def runMax (σ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun u => logPrice σ c B u ω) '' Set.Icc 0 t)

/-- The running minimum `I_t = inf {X_u : u ≤ t}` (§1, p. 505), the infimum of the log-price over
`u ∈ [0, t]`. -/
noncomputable def runMin (σ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  sInf ((fun u => logPrice σ c B u ω) '' Set.Icc 0 t)

/-- The high–low–close statistic at time `t`, `S_t (S_t − X_t) + I_t (I_t − X_t)`; at `t = 1` it is
the estimator `σ̂² ≡ S_1(S_1 − X_1) + I_1(I_1 − X_1)` of display (2), p. 505. -/
noncomputable def estimator (σ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)
    + runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)

/-- The rate `α ≡ (√(c² + 2λσ²) − c)/σ²` of the exponential law of `S_T` (§2, p. 505), where `lam`
is the rate `λ` of the exponential time `T`. Meaningful for `σ > 0`. -/
noncomputable def alpha (σ c lam : ℝ) : ℝ :=
  (Real.sqrt (c ^ 2 + 2 * lam * σ ^ 2) - c) / σ ^ 2

/-- The rate `β ≡ (√(c² + 2λσ²) + c)/σ²` of the exponential law of `−I_T` (§2, p. 505).
Meaningful for `σ > 0`. -/
noncomputable def beta (σ c lam : ℝ) : ℝ :=
  (Real.sqrt (c ^ 2 + 2 * lam * σ ^ 2) + c) / σ ^ 2

end RogersSatchell.Unbiased


