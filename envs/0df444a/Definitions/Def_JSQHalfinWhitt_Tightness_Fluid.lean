-- Prove2me | Definitions.Def_JSQHalfinWhitt_Tightness_Fluid
-- name    : JSQHalfinWhitt_Tightness_Fluid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:06.860789+00:00
-- url     : https://prove2.me/theorems/836c026a-8b2d-4813-a5ce-a9976dd9d445
-- title:
--   Fluid-model objects: the system (4.8), $\nu^*$, $\eta^*$, the curve $\Gamma^{(\kappa)}$, the arc $\gamma^{(\kappa)}$, the hitting time $\tau$ and $f^*$ of (4.14)
-- statement:
--   Fix $n \ge 1$, $\beta > 0$ and $\kappa$.
--
--   1. **The system (4.8).** For $x_1 \le 0$, the unknowns $(\nu, \eta)$ satisfy
--   $$-\beta/\sqrt n + (x_1 + \beta/\sqrt n)e^{-\eta} + \eta\nu e^{-\eta} = 0,\qquad \nu e^{-\eta} = \kappa/\sqrt n,\qquad \nu \ge \kappa/\sqrt n,\quad \eta \ge 0.$$
--      When it has exactly one solution, that solution is $(\nu^*(x_1), \eta^*(x_1))$ (Lemma 5 shows this is the case for $\kappa \ge \beta$).
--   2. **The curve and the arc.** $\Gamma^{(\kappa)} = \{x \in \Omega \mid x_2 = \nu^*(x_1)\}$, and one writes $x > \Gamma^{(\kappa)}$ when $x_2 > \nu^*(x_1)$, and $x \ge \Gamma^{(\kappa)}$, $x < \Gamma^{(\kappa)}$, $x \le \Gamma^{(\kappa)}$ similarly (4.9). The arc $\gamma^{(\kappa)}(x_1)$ is the set of points
--   $$\big(-\beta/\sqrt n + (x_1 + \beta/\sqrt n)e^{-t} + t\nu^*(x_1)e^{-t},\ \nu^*(x_1)e^{-t}\big),\qquad t \in [0, \eta^*(x_1)].$$
--   3. **The hitting time.** $\tau(x)$ is the smallest solution $\eta \ge 0$ of
--   $$\beta/\sqrt n - (x_1 + \beta/\sqrt n)e^{-\eta} - \eta x_2 e^{-\eta} = 0,$$
--      and $\tau(x) = \infty$ if there is none.
--   4. **The function (4.14).** For $\kappa > \beta$,
--   $$f^*(x) = \begin{cases} 0, & x_2 \in [0, \kappa/\sqrt n],\\ x_2 - \frac{\kappa}{\sqrt n} - \frac{\kappa}{\sqrt n}\log(\sqrt n x_2/\kappa), & x \le \Gamma^{(\kappa)} \text{ and } x_2 \ge \kappa/\sqrt n,\\ x_2(1 - e^{-\tau(x)}) - \frac{\kappa}{\sqrt n}\tau(x) + \frac12\frac{\sqrt n}{\beta}\big(x_2 e^{-\tau(x)} - \kappa/\sqrt n\big)^2, & x \ge \Gamma^{(\kappa)}. \end{cases}$$
--
--   These are the objects of the fluid-model analysis that produces the Lyapunov function $f^*$ solving the PDE of Lemma 4. $\Gamma^{(\kappa)}$ is the set of initial conditions whose fluid path first meets the vertical axis at $(0, \kappa/\sqrt n)$, and $\tau(x)$ is the time at which the fluid path from $x$ first hits the vertical axis.
--
--   **Formalization Note** `nuStar`/`etaStar` are the components of the unique solution of (4.8) when it exists and is unique, and `0` otherwise; Lemma 5 is the statement that the solution exists and is unique. The relations $x \gtrless \Gamma^{(\kappa)}$ are written directly as inequalities between `x.2` and `nuStar β κ n x.1`. $\tau$ takes values in `WithTop ℝ`, with $\infty$ encoded as `⊤`, so that a missing solution is not silently replaced by `0`. When the solution set is nonempty, `sInf` of it is its least element, because the set is closed and bounded below. The paper states $\tau$ for $x \in (-\infty, 0] \times [\kappa/\sqrt n, \infty)$; the same formula is used at every $x$, as in (4.10). `tauR` is the real value of $\tau$ where it is finite and `0` elsewhere; it appears only at points where $\tau$ is asserted to be finite. $f^*$ is an `if` cascade taking the first applicable branch, with the zero branch first, then the middle branch, then the upper branch; Lemma 7's "well-defined" clause is the agreement of the branches on the overlaps. $f^*$ is defined by the closed form (4.14), not through the fluid model (4.1).
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 12 (Lemma 5, (4.8), Γ^{(κ)}, γ^{(κ)}, (4.9)), p. 13 (Lemma 6, τ), p. 15 ((4.14))

import Mathlib

namespace JSQHalfinWhitt.Tightness

open scoped Classical

/-- The nonlinear system (4.8) of Lemma 5 (Braverman, p. 12) in the unknowns `(ν, η)`, for fixed
`κ` and `x_1`:
`−β/√n + (x_1 + β/√n) e^{−η} + η ν e^{−η} = 0`, `ν e^{−η} = κ/√n`, `ν ≥ κ/√n`, `η ≥ 0`. -/
def FluidSystem (β κ : ℝ) (n : ℕ) (x1 ν η : ℝ) : Prop :=
  -(β / Real.sqrt n) + (x1 + β / Real.sqrt n) * Real.exp (-η) + η * ν * Real.exp (-η) = 0 ∧
    ν * Real.exp (-η) = κ / Real.sqrt n ∧ κ / Real.sqrt n ≤ ν ∧ 0 ≤ η

/-- `ν^*(x_1)`: the `ν`-component of the unique solution of (4.8) when the solution exists and is
unique (Lemma 5 asserts this for `κ ≥ β`, `x_1 ≤ 0`); `0` otherwise. -/
noncomputable def nuStar (β κ : ℝ) (n : ℕ) (x1 : ℝ) : ℝ :=
  if h : ∃! p : ℝ × ℝ, FluidSystem β κ n x1 p.1 p.2 then (Classical.choose h.exists).1 else 0

/-- `η^*(x_1)`: the `η`-component of the unique solution of (4.8) when the solution exists and is
unique; `0` otherwise. -/
noncomputable def etaStar (β κ : ℝ) (n : ℕ) (x1 : ℝ) : ℝ :=
  if h : ∃! p : ℝ × ℝ, FluidSystem β κ n x1 p.1 p.2 then (Classical.choose h.exists).2 else 0

/-- The curve `Γ^{(κ)} = {x ∈ Ω | x_2 = ν^*(x_1)}` of Lemma 5, with `Ω = (−∞, 0] × [0, ∞)`.
The order convention (4.9) writes `x > Γ^{(κ)}` for `x_2 > ν^*(x_1)`, and `x ≥ Γ^{(κ)}`,
`x < Γ^{(κ)}`, `x ≤ Γ^{(κ)}` similarly; in Lean these are stated directly as inequalities between
`x.2` and `nuStar β κ n x.1`. -/
def gammaCurve (β κ : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {x | x.1 ≤ 0 ∧ 0 ≤ x.2 ∧ x.2 = nuStar β κ n x.1}

/-- The arc `γ^{(κ)}(x_1)` of Lemma 5: the points
`(−β/√n + (x_1 + β/√n) e^{−t} + t ν^*(x_1) e^{−t}, ν^*(x_1) e^{−t})` for `t ∈ [0, η^*(x_1)]`. -/
def gammaArc (β κ : ℝ) (n : ℕ) (x1 : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ etaStar β κ n x1 ∧
    p = (-(β / Real.sqrt n) + (x1 + β / Real.sqrt n) * Real.exp (-t) +
          t * nuStar β κ n x1 * Real.exp (-t), nuStar β κ n x1 * Real.exp (-t))}

/-- The hitting-time equation of Lemma 6 (p. 13) at `x = (x_1, x_2)`:
`β/√n − (x_1 + β/√n) e^{−η} − η x_2 e^{−η} = 0`. -/
def HitEq (β : ℝ) (n : ℕ) (x : ℝ × ℝ) (η : ℝ) : Prop :=
  β / Real.sqrt n - (x.1 + β / Real.sqrt n) * Real.exp (-η) - η * x.2 * Real.exp (-η) = 0

/-- `τ(x)` of Lemma 6: the smallest solution `η ≥ 0` of the hitting-time equation, and `∞` (`⊤`)
if it has no solution `η ≥ 0`. The solution set is closed and bounded below by `0`, so when it
is nonempty its infimum is its least element. The paper states the definition for
`x ∈ (−∞, 0] × [κ/√n, ∞)`; the same formula is used at every `x`. -/
noncomputable def tau (β : ℝ) (n : ℕ) (x : ℝ × ℝ) : WithTop ℝ :=
  if ∃ η : ℝ, 0 ≤ η ∧ HitEq β n x η then ((sInf {η : ℝ | 0 ≤ η ∧ HitEq β n x η} : ℝ) : WithTop ℝ)
  else ⊤

/-- The real value of `τ(x)` where it is finite (`0` where `τ(x) = ∞`; every statement that uses
`tauR` restricts to points where `τ` is finite). -/
noncomputable def tauR (β : ℝ) (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  (tau β n x).untopD 0

/-- The middle branch of (4.14), used for `x ≤ Γ^{(κ)}` and `x_2 ≥ κ/√n`:
`x_2 − κ/√n − (κ/√n) log(√n x_2/κ)`. -/
noncomputable def fStarMid (κ : ℝ) (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  x.2 - κ / Real.sqrt n - κ / Real.sqrt n * Real.log (Real.sqrt n * x.2 / κ)

/-- The upper branch of (4.14), used for `x ≥ Γ^{(κ)}`:
`x_2 (1 − e^{−τ(x)}) − (κ/√n) τ(x) + (1/2)(√n/β)(x_2 e^{−τ(x)} − κ/√n)^2`. -/
noncomputable def fStarUpper (β κ : ℝ) (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  x.2 * (1 - Real.exp (-tauR β n x)) - κ / Real.sqrt n * tauR β n x +
    1 / 2 * (Real.sqrt n / β) * (x.2 * Real.exp (-tauR β n x) - κ / Real.sqrt n) ^ 2

/-- The function `f^*` of (4.14) (p. 15), for `κ > β`:
`f^*(x) = 0` if `x_2 ∈ [0, κ/√n]`; the middle branch if `x ≤ Γ^{(κ)}` and `x_2 ≥ κ/√n`; the upper
branch if `x ≥ Γ^{(κ)}`. The three regions cover `Ω` and overlap only on their boundaries; this
`if` cascade takes the first applicable branch, and Lemma 7's "well-defined" clause is that the
branches agree on the overlaps. -/
noncomputable def fStar (β κ : ℝ) (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  if x.2 ≤ κ / Real.sqrt n then 0
  else if x.2 ≤ nuStar β κ n x.1 then fStarMid κ n x
  else fStarUpper β κ n x

end JSQHalfinWhitt.Tightness


