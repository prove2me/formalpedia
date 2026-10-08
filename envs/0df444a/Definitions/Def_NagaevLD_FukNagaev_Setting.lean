-- Prove2me | Definitions.Def_NagaevLD_FukNagaev_Setting
-- name    : NagaevLD_FukNagaev_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:04.213657+00:00
-- url     : https://prove2.me/theorems/f5d06c04-6933-496c-bdf4-5c0e38a3bbf2
-- title:
--   §0–§1, pp. 745, 747–749 — S_n, the truncation X̃_i, S̃_n, the truncated sums μ(−∞, Y), B²(−∞, Y), A(t; 0, Y), A_t⁺, B_n², the bounds P₄, P₅, P₆ and conditions (1.4), (1.6)
-- statement:
--   This file fixes the objects of §0–§1 of Nagaev's survey. Let $X_1,\dots,X_n$ be real random variables on a probability space $(\Omega,\mathcal F,P)$, with distribution functions $F_i(u)=P(X_i<u)$, and put $S_n=X_1+\dots+X_n$. Let $Y=\{y_1,\dots,y_n\}$ be positive truncation levels.
--
--   1. **Truncation.** $\tilde X_i = X_i$ if $X_i\le y_i$ and $\tilde X_i=0$ if $X_i>y_i$; $\tilde S_n=\tilde X_1+\dots+\tilde X_n$.
--   2. **Truncated moment sums.** The paper writes $\mu(\cdot,\cdot)$, $B^2(\cdot,\cdot)$, $A(t;\cdot,\cdot)$ for sums of truncated means, second moments and absolute moments of order $t$, the arguments being the truncation levels. Three of them are used here:
--   $$\mu(-\infty,Y)=\sum_{i=1}^n\int_{u\le y_i}u\,dF_i(u),\qquad B^2(-\infty,Y)=\sum_{i=1}^n\int_{u\le y_i}u^2\,dF_i(u),\qquad A(t;0,Y)=\sum_{i=1}^n\int_{0\le u\le y_i}|u|^t\,dF_i(u).$$
--   The page prints $\mu(-\infty,Y)$ explicitly; $B^2(-\infty,Y)$ and $A(t;0,Y)$ are obtained from its examples by the same rule. Also $A_t^+=\sum_i\int_{u\ge0}u^t\,dF_i(u)$ and $B_n^2=\sum_i\operatorname{Var}X_i$.
--   3. **The bounds of the case $t\ge2$** (p. 748), for $0<\alpha<1$, $\beta$ and $y>0$, with $\mu=\mu(-\infty,Y)$, $B^2=B^2(-\infty,Y)$, $A=A(t;0,Y)$:
--   $$P_4=\exp\Big\{\beta\frac xy-\Big(\big(1-\tfrac\alpha2\big)\frac xy-\frac{\mu}{y}\Big)\log\Big(\frac{\beta xy^{t-1}}{A}+1\Big)\Big\},$$
--   $$P_5=\exp\Big\{\Big(\beta-\frac{t\alpha}2\Big)\frac xy-\Big(\beta\frac xy-\frac{\mu}{y}\Big)\log\Big(\frac{\beta xy^{t-1}}{A}+1\Big)\Big\},\qquad P_6=\exp\Big\{-\frac{\alpha x(\alpha x/2-\mu)}{e^tB^2}\Big\}.$$
--   4. **The case conditions of Theorem 1.3:** (1.4) is $\max[t,\log(\beta xy^{t-1}/A+1)]\ge\alpha xy/(e^tB^2)$ and (1.6) is the reverse strict inequality.
--
--   These are the quantities in which the Fuk–Nagaev inequality bounds $P(S_n\ge x)$.
--
--   **Formalization Note** The summands are indexed by `Fin n` (index $i$ stands for the paper's $i+1$). Every integral $\int_{E}\varphi(u)\,dF_i(u)$ is written as the expectation of $\varphi(X_i)$ over the event $\{X_i\in E\}$; the events are copied with their endpoints ($u\le y_i$, $0\le u\le y_i$, $u\ge0$). Powers $|u|^t$ are real powers. $P_4,P_5,P_6$ and the two conditions are functions of the scalars $t,\alpha,\beta,x,y,\mu,B^2,A$. Lean divides by $0$ to give $0$, so on the page's degenerate value $A(t;0,Y)=0$ (logarithm $=+\infty$) condition (1.4) would read wrongly; `cond_1_4` therefore contains the disjunct $A=0$, and `cond_1_6` the conjunct $0<A$. With these, for $A\ge0$ the two conditions are exact complements, as on the page. Statements using $B^2(-\infty,Y)$ or $B_n^2$ assume the corresponding second moments are finite (Lean's integral of a non-integrable function is $0$); finiteness of $B^2(-\infty,Y)$ also makes $\mu(-\infty,Y)$ finite, and the integrand of $A(t;0,Y)$ is bounded by $y_i^t$. At $B^2(-\infty,Y)=0$ under Theorem 1.3's hypotheses, each truncated $X_i$ vanishes almost surely, so $\mu(-\infty,Y)=A(t;0,Y)=0$; `P6` explicitly takes the paper's limiting value $0$ there.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), pp. 745 (§0), 747–748 (notation, P₄–P₆), 749 (Theorem 1.3, (1.4), (1.6), X̃_i, S̃_n)

import Mathlib

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

/-- `S n X` is the sum `S_n = X₁ + ⋯ + X_n` (Nagaev 1979, §0, p. 745). The summands are indexed by
`Fin n`, i.e. `X 0, …, X (n-1)` stand for the paper's `X₁, …, X_n`. -/
def S {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, X i ω

/-- The truncated summand `X̃_i = X_i` if `X_i ≤ y_i`, `= 0` if `X_i > y_i` (proof of Theorem 1.3,
p. 749). -/
noncomputable def Xt {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (i : Fin n)
    (ω : Ω) : ℝ :=
  if X i ω ≤ yv i then X i ω else 0

/-- The truncated sum `S̃_n = X̃₁ + ⋯ + X̃_n` (proof of Theorem 1.3, p. 749). -/
noncomputable def St {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (ω : Ω) : ℝ :=
  ∑ i, Xt X yv i ω

/-- `μ(−∞, Y) = Σ ∫_{u ≤ y_i} u dF_i(u) = Σ E[X_i; X_i ≤ y_i]` (p. 748). -/
noncomputable def muY {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | X i ω ≤ yv i}, X i ω ∂P

/-- `B²(−∞, Y) = Σ ∫_{u ≤ y_i} u² dF_i(u) = Σ E[X_i²; X_i ≤ y_i]` (notation rule of pp. 747–748).
Every statement using it assumes `X_i²` is integrable on `{X_i ≤ y_i}` (the paper's finite
`B²(−∞, Y)`); otherwise Lean's Bochner integral would return `0` instead of `+∞`. -/
noncomputable def B2Y {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | X i ω ≤ yv i}, X i ω ^ 2 ∂P

/-- `A(t; 0, Y) = Σ ∫_{0 ≤ u ≤ y_i} |u|^t dF_i(u) = Σ E[|X_i|^t; 0 ≤ X_i ≤ y_i]` (notation rule of
pp. 747–748), with the real power `Real.rpow`. -/
noncomputable def AY {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | 0 ≤ X i ω ∧ X i ω ≤ yv i}, |X i ω| ^ t ∂P

/-- `A_t⁺ = Σ ∫_{u ≥ 0} u^t dF_i(u) = Σ E[|X_i|^t; X_i ≥ 0]` (§0, p. 745). -/
noncomputable def Atplus {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∫ ω in {ω | 0 ≤ X i ω}, |X i ω| ^ t ∂P

/-- `B_n² = Σ σ_i²`, `σ_i² = Var X_i` (§0, p. 745). Mathlib's `variance` is `0` for a variable not
in `L²`; every statement using `Bn2` assumes `MemLp (X i) 2 P`. -/
noncomputable def Bn2 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (X : Fin n → Ω → ℝ) : ℝ :=
  ∑ i, variance (X i) P

/-- `P₄ = exp{β x/y − ((1 − α/2) x/y − μ/y) · log(β x y^{t−1}/A + 1)}` (p. 748), as a function of
the scalars `t, α, β, x, y`, `μ = μ(−∞, Y)` and `A = A(t; 0, Y)`. -/
noncomputable def P4 (t α β x y μ A : ℝ) : ℝ :=
  Real.exp (β * x / y - ((1 - α / 2) * x / y - μ / y) * Real.log (β * x * y ^ (t - 1) / A + 1))

/-- `P₅ = exp{(β − tα/2) x/y − (β x/y − μ/y) · log(β x y^{t−1}/A + 1)}` (p. 748). -/
noncomputable def P5 (t α β x y μ A : ℝ) : ℝ :=
  Real.exp ((β - t * α / 2) * x / y - (β * x / y - μ / y) * Real.log (β * x * y ^ (t - 1) / A + 1))

/-- `P₆ = exp{−αx(αx/2 − μ)/(e^t B)}` (p. 748), with `μ = μ(−∞, Y)` and
`B = B²(−∞, Y)`. At `B = 0` under the hypotheses of Theorem 1.3, also `μ = 0`, and the
paper's expression has limit `0`; use that value instead of Lean's division-by-zero value. -/
noncomputable def P6 (t α x μ B : ℝ) : ℝ :=
  if B = 0 then 0 else Real.exp (-(α * x * (α * x / 2 - μ) / (Real.exp t * B)))

/-- Condition (1.4) of Theorem 1.3 (p. 749):
`max[t, log(βxy^{t−1}/A + 1)] ≥ αxy/(e^t B)`, with `A = A(t; 0, Y)`, `B = B²(−∞, Y)`.
On the page `A = 0` makes the logarithm `+∞`, so (1.4) holds; this is the disjunct `A = 0`. -/
noncomputable def cond_1_4 (t α β x y B A : ℝ) : Prop :=
  A = 0 ∨ α * x * y / (Real.exp t * B) ≤ max t (Real.log (β * x * y ^ (t - 1) / A + 1))

/-- Condition (1.6) of Theorem 1.3 (p. 749):
`max[t, log(βxy^{t−1}/A + 1)] < αxy/(e^t B)`, which on the page forces `A = A(t; 0, Y)` finite
and nonzero; for `A ≥ 0` it is the exact complement of `cond_1_4`. -/
noncomputable def cond_1_6 (t α β x y B A : ℝ) : Prop :=
  0 < A ∧ max t (Real.log (β * x * y ^ (t - 1) / A + 1)) < α * x * y / (Real.exp t * B)

end NagaevLD.FukNagaev


