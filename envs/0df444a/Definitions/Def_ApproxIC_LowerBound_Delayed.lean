-- Prove2me | Definitions.Def_ApproxIC_LowerBound_Delayed
-- name    : ApproxIC_LowerBound_Delayed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:28.99438+00:00
-- url     : https://prove2.me/theorems/e63ca34f-b5df-4ffe-a622-abe374e4564c
-- title:
--   §5.1, eq. (13), Proposition 3, Lemma 6, eq. (25) — perturbed delayed mechanisms: v⋆(·|µ,δ), w, (ODE)-(DDE), m_pd = (x_pd, t_pd), Γ, y_pd
-- statement:
--   This file defines the objects of §5.1 of Balseiro, Besbes and Castro, the building blocks of the randomized mechanisms behind the lower bound of Theorem 3. Throughout, $p^\star$, $\mu$, $\delta$, $\varepsilon$ are real parameters (in the paper $0<\delta<p^\star$ and $p^\star+\delta+\mu<\bar v$).
--
--   1. **The best reporting function** (eq. (13)):
--   $$v^\star(v\,|\,\mu,\delta)=\begin{cases}0 & v\in[0,p^\star-\delta),\\ v-\mu & v\in[p^\star-\delta,p^\star+\delta+\mu],\\ p^\star+\delta & v\in[p^\star+\delta+\mu,\bar v].\end{cases}$$
--   2. **Its generalized inverse** $w(v)=p^\star-\delta$ for $v\in[0,p^\star-\delta-\mu]$ and $w(v)=v+\mu$ for $v\in[p^\star-\delta-\mu,p^\star+\delta]$.
--   3. **Solutions of (ODE)-(DDE).** A function $x$ solves the system of Proposition 3 on $[0,p^\star+\delta]$ if
--   $$\dot x(v)=\frac{x(v)}{w(v)-v}\ \ \forall v\in[0,p^\star-\delta],\qquad x(0)=\frac{\varepsilon}{p^\star-\delta},\qquad \dot x(v)=\frac{x(v)-x(v^\star(v))}{w(v)-v}\ \ \forall v\in[p^\star-\delta,p^\star+\delta].$$
--   The derivative in each equation is taken within its closed interval, so it is one-sided at the endpoints; at $v=p^\star-\delta$ the left derivative is governed by (ODE) and the right derivative by (DDE).
--   4. **The perturbed delayed mechanism** $m_{pd}=(x_{pd},t_{pd})$: $x_{pd}=x$ on $[0,p^\star+\delta]$, $x_{pd}=1$ on $(p^\star+\delta,\bar v]$, and
--   $$t_{pd}(v)=\begin{cases}v\,x_{pd}(v) & v<p^\star-\delta,\\ v\,x_{pd}(v)-\int_0^v x_{pd}(v^\star(s))\,ds+\varepsilon & v\ge p^\star-\delta.\end{cases}$$
--   5. **The function of Lemma 6**:
--   $$\Gamma(t)=\sum_{j=0}^{\lfloor t\rfloor+1}\frac{(-1)^j e^{-j}}{j!}\,(t+1-j)^j,\qquad t\ge 0.$$
--   6. **The closed form of eq. (25)** (proof of Proposition 4): $y_{pd}(v)=\frac{\mu}{p^\star-\delta-v}\exp\!\big(-\frac{v-p^\star+\delta+\mu}{\mu}\big)$ for $v\le p^\star-\delta-\mu$, $y_{pd}(v)=1$ for $v\in[p^\star-\delta-\mu,p^\star-\delta]$, and $y_{pd}(v)=\Gamma\big(\frac{v-p^\star+\delta}{\mu}\big)$ for $v\in[p^\star-\delta,p^\star+\delta]$, which is the sum printed in (25).
--
--   These objects are the vocabulary of Propositions 3–6 and Lemmas 5–6.
--
--   **Formalization Note** All functions are total on $\mathbb R$. $x_{pd}$ is set to $0$ below $0$, which plays no role on $S$. One-sided derivatives at $p^\star-\delta$ are essential: the right-hand sides of (ODE) and (DDE) differ there (the delay term $x(p^\star-\delta-\mu)$ is positive), so a two-sided derivative would make the system unsolvable. $\Gamma$ is the paper's sum with natural-number powers and $\lfloor t\rfloor$ the natural floor; it is used only for $t\ge0$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 30, eq. (13); p. 31, w and Proposition 3 ((ODE), (DDE), x_pd, t_pd); p. 60, Lemma 6 (Γ); pp. 55–56, proof of Proposition 4, eq. (25)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Setting

/-!
# Perturbed delayed mechanisms (Balseiro, Besbes, Castro, arXiv:2103.03403v2, §5.1, pp. 30–31; App. C)

The objects of §5.1, for reals `pstar` (the price `p⋆`), `μ`, `δ`, `ε` and a function `x`:
the best reporting function `v⋆(·|μ, δ)` of eq. (13), its generalized inverse `w`, the solutions
of the system (ODE)-(DDE), the perturbed delayed mechanism `m_pd = (x_pd, t_pd)`, the function `Γ`
of Lemma 6 and the change of variables `y_pd` of the proof of Proposition 4 (eq. (25)).
All are total functions `ℝ → ℝ`; only their values on `[0, v̄]` matter.
-/

namespace ApproxIC.LowerBound

open MeasureTheory

/-- `v⋆(v|μ, δ)` of eq. (13), p. 30: `0` if `v ∈ [0, p⋆ − δ)`, `v − μ` if `v ∈ [p⋆ − δ, p⋆ + δ + μ]`,
and `p⋆ + δ` if `v ∈ [p⋆ + δ + μ, v̄]`. -/
noncomputable def vstarPD (pstar μ δ : ℝ) (v : ℝ) : ℝ :=
  if v < pstar - δ then 0 else if v ≤ pstar + δ + μ then v - μ else pstar + δ

/-- The generalized inverse `w` of `v⋆`, p. 31: `p⋆ − δ` if `v ∈ [0, p⋆ − δ − μ]`, and `v + μ` if
`v ∈ [p⋆ − δ − μ, p⋆ + δ]`. -/
noncomputable def wPD (pstar μ δ : ℝ) (v : ℝ) : ℝ :=
  if v ≤ pstar - δ - μ then pstar - δ else v + μ

/-- `x` solves the system (ODE)-(DDE) of Proposition 3, p. 31, on `[0, p⋆ + δ]`:
* `x(0) = ε / (p⋆ − δ)`;
* (ODE) `ẋ(v) = x(v) / (w(v) − v)` for `v ∈ [0, p⋆ − δ]`;
* (DDE) `ẋ(v) = (x(v) − x(v⋆(v))) / (w(v) − v)` for `v ∈ [p⋆ − δ, p⋆ + δ]`.

The derivatives are taken within the closed interval of each equation, so they are one-sided at
the endpoints, in particular at the shared point `p⋆ − δ` (left derivative from (ODE), right
derivative from (DDE)). -/
def IsPDSolution (pstar μ δ ε : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = ε / (pstar - δ) ∧
  (∀ v ∈ Set.Icc 0 (pstar - δ),
    HasDerivWithinAt x (x v / (wPD pstar μ δ v - v)) (Set.Icc 0 (pstar - δ)) v) ∧
  (∀ v ∈ Set.Icc (pstar - δ) (pstar + δ),
    HasDerivWithinAt x ((x v - x (vstarPD pstar μ δ v)) / (wPD pstar μ δ v - v))
      (Set.Icc (pstar - δ) (pstar + δ)) v)

/-- The allocation `x_pd` of Proposition 3, p. 31: the solution `x` on `[0, p⋆ + δ]` and
`x_pd(v) = 1` for `v ∈ (p⋆ + δ, v̄]`. (The value `0` below `0` plays no role.) -/
noncomputable def xPD (x : ℝ → ℝ) (pstar δ : ℝ) (v : ℝ) : ℝ :=
  if v < 0 then 0 else if v ≤ pstar + δ then x v else 1

/-- The payment `t_pd` of Proposition 3, p. 31: `t_pd(v) = v · x_pd(v)` if `v < p⋆ − δ`, and
`t_pd(v) = v · x_pd(v) − ∫_0^v x_pd(v⋆(s)) ds + ε` if `v ≥ p⋆ − δ`. -/
noncomputable def tPD (x : ℝ → ℝ) (pstar μ δ ε : ℝ) (v : ℝ) : ℝ :=
  if v < pstar - δ then v * xPD x pstar δ v
  else v * xPD x pstar δ v - (∫ s in (0)..v, xPD x pstar δ (vstarPD pstar μ δ s)) + ε

/-- The perturbed delayed mechanism `m_pd = (x_pd, t_pd)` (Proposition 3, p. 31). -/
noncomputable def mPD (x : ℝ → ℝ) (pstar μ δ ε : ℝ) : ApproxIC.UpperBound.Mech :=
  ⟨xPD x pstar δ, tPD x pstar μ δ ε⟩

/-- `Γ(t) = ∑_{j=0}^{⌊t⌋+1} ((−1)^j e^{−j} / j!) (t + 1 − j)^j` (Lemma 6, p. 60; used for `t ≥ 0`). -/
noncomputable def Gamma (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (⌊t⌋₊ + 2),
    (-1 : ℝ) ^ j * Real.exp (-(j : ℝ)) / (j.factorial : ℝ) * (t + 1 - j) ^ j

/-- The closed form `y_pd` of eq. (25) (proof of Proposition 4, pp. 55–56):
`y_pd(v) = (μ / (p⋆ − δ − v)) · exp(−(v − p⋆ + δ + μ)/μ)` if `v ≤ p⋆ − δ − μ`;
`y_pd(v) = 1` if `v ∈ [p⋆ − δ − μ, p⋆ − δ]`;
`y_pd(v) = ∑_{j=0}^{⌊(v−p⋆+δ)/μ⌋+1} ((−1)^j e^{−j}/j!) ((v − p⋆ + δ)/μ + 1 − j)^j = Γ((v − p⋆ + δ)/μ)`
if `v ∈ [p⋆ − δ, p⋆ + δ]`. -/
noncomputable def yPD (pstar μ δ : ℝ) (v : ℝ) : ℝ :=
  if v ≤ pstar - δ - μ then μ / (pstar - δ - v) * Real.exp (-((v - pstar + δ + μ) / μ))
  else if v ≤ pstar - δ then 1
  else Gamma ((v - pstar + δ) / μ)

end ApproxIC.LowerBound


