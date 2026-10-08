-- Prove2me | Definitions.Def_JSQHalfinWhitt_Tightness_PDE
-- name    : JSQHalfinWhitt_Tightness_PDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:08.011981+00:00
-- url     : https://prove2.me/theorems/f6f65e48-1e75-4d3e-8f64-fa69d588959d
-- title:
--   The domain $\Omega$, one-sided partials with absolutely continuous first derivatives, the operator $L$ (3.4), the PDE (3.7)–(3.8) and the bounds (3.9)–(3.11)
-- statement:
--   Let $\Omega = (-\infty, 0] \times [0, \infty)$ (1.4). Partial derivatives of a function on $\Omega$ are one-sided on the boundary $\partial\Omega$ where the two-sided derivative is not defined; $f_i$ denotes the partial derivative in $x_i$.
--
--   1. **Regularity.** $f$ has partial derivatives $f_1, f_2$ on $\Omega$ with absolutely continuous first partials and weak second derivatives $f_{11}, f_{22}$ if
--      - $f_1(x)$ is the derivative of $t \mapsto f(t, x_2)$ at $t = x_1$ for every $x \in \Omega$, from the left when $x_1 = 0$;
--      - $f_2(x)$ is the derivative of $t \mapsto f(x_1, t)$ at $t = x_2$ for every $x \in \Omega$, from the right when $x_2 = 0$;
--      - for every $x_2 \ge 0$ and $a \le b \le 0$, $f_1(b, x_2) - f_1(a, x_2) = \int_a^b f_{11}(u, x_2)\,du$ with an integrable integrand;
--      - for every $x_1 \le 0$ and $0 \le a \le b$, $f_2(x_1, b) - f_2(x_1, a) = \int_a^b f_{22}(x_1, u)\,du$ with an integrable integrand.
--
--      The last two items say that $f_1(\cdot, x_2)$ and $f_2(x_1, \cdot)$ are absolutely continuous on compact intervals with a.e. derivatives $f_{11}$, $f_{22}$.
--   2. **Mixed weak derivative.** $f_{12}$ is a mixed weak derivative when $f_1(x_1, b) - f_1(x_1, a) = \int_a^b f_{12}(x_1, u)\,du$ for $x_1 \le 0$, $0 \le a \le b$.
--   3. **The operator (3.4).**
--   $$Lf(x) = \big(-x_1 + x_2 - \beta/\sqrt n\big) f_1(x) - x_2 f_2(x).$$
--   4. **The PDE (3.7)–(3.8).**
--   $$Lf(x) = -\big((x_2 - \kappa/\sqrt n) \vee 0\big),\quad x \in \Omega,\qquad f_1(0, x_2) = f_2(0, x_2),\quad x_2 \ge 0.$$
--   5. **The bounds (3.9)–(3.11).** $f_{11}, f_{12}, f_{22} \ge 0$ on $\Omega$; $f_{11} = f_{22} = 0$ where $x_2 \in [0, \kappa/\sqrt n]$; and where $x_2 \ge \kappa/\sqrt n$,
--   $$f_{11}(x) \le \frac{\sqrt n}{\beta}\Big(\frac{\kappa}{\kappa - \beta} + 1\Big),\qquad f_{22}(x) \le \frac{\sqrt n}{\beta}\Big(5 + \frac{2\kappa}{\kappa - \beta}\Big).$$
--
--   These notions state the generator expansion (Lemma 3) and the existence of the Lyapunov function $f^*$ (Lemmas 4 and 7).
--
--   **Formalization Note** Points of $\Omega$ are pairs `(x₁, x₂) : ℝ × ℝ`. The partial derivatives are named functions asserted, through `HasDerivWithinAt` along each coordinate line restricted to $\Omega$'s slice (`Set.Iic 0` in $x_1$, `Set.Ici 0` in $x_2$), to be the derivatives, so no junk value of `deriv` is ever used. The weak second derivatives are given in the literal form "a.e. derivative of an absolutely continuous function", through the integral representation on every compact interval of the line (Lebesgue's characterization). Pointwise inequalities on an existentially chosen weak derivative are equivalent to a.e. inequalities, since a weak derivative may be changed on a null set. Values of $f$ outside $\Omega$ play no role. The paper writes $f_{12}$ in (3.9) and uses it in the proof as $f_{21} \ge 0$; the two mixed derivatives coincide for the functions concerned, and the paper's index order (the $x_2$-derivative of $f_1$) is kept.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 4 ((1.4), one-sided derivative convention), p. 7 ((3.4)), p. 8 (Lemma 4, (3.7)–(3.11))

import Mathlib

namespace JSQHalfinWhitt.Tightness

open MeasureTheory

/-- The domain `Ω = (−∞, 0] × [0, ∞)` of (1.4) (Braverman, p. 4). Points are pairs
`x = (x_1, x_2)`. -/
def Omega : Set (ℝ × ℝ) :=
  Set.Iic (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)

/-- `f : Ω → ℝ` has first partial derivatives `f_1, f_2` on `Ω`, with `f_1(·, x_2)` and
`f_2(x_1, ·)` absolutely continuous along every line of `Ω` and with a.e. derivatives
(second-order weak derivatives) `f_11` and `f_22`:

1. `f_1(x)` is the partial derivative of `f` in `x_1` at every `x ∈ Ω`, one-sided (from the left)
   on the boundary `x_1 = 0`;
2. `f_2(x)` is the partial derivative of `f` in `x_2` at every `x ∈ Ω`, one-sided (from the right)
   on the boundary `x_2 = 0`;
3. for every `x_2 ≥ 0` and `a ≤ b ≤ 0`, `u ↦ f_11(u, x_2)` is integrable on `[a, b]` and
   `f_1(b, x_2) − f_1(a, x_2) = ∫_a^b f_11(u, x_2) du`;
4. for every `x_1 ≤ 0` and `0 ≤ a ≤ b`, `u ↦ f_22(x_1, u)` is integrable on `[a, b]` and
   `f_2(x_1, b) − f_2(x_1, a) = ∫_a^b f_22(x_1, u) du`.

Items 3 and 4 say exactly that `f_1(·, x_2)` and `f_2(x_1, ·)` are absolutely continuous on every
compact interval of the line inside `Ω`, with a.e. derivatives `f_11(·, x_2)` and `f_22(x_1, ·)`
(Lebesgue's characterization of absolute continuity). Values of `f` outside `Ω` play no role. -/
def IsWeakC2 (f f1 f2 f11 f22 : ℝ × ℝ → ℝ) : Prop :=
  (∀ x ∈ Omega, HasDerivWithinAt (fun t => f (t, x.2)) (f1 x) (Set.Iic 0) x.1) ∧
  (∀ x ∈ Omega, HasDerivWithinAt (fun t => f (x.1, t)) (f2 x) (Set.Ici 0) x.2) ∧
  (∀ x2 : ℝ, 0 ≤ x2 → ∀ a b : ℝ, a ≤ b → b ≤ 0 →
      IntervalIntegrable (fun u => f11 (u, x2)) volume a b ∧
        f1 (b, x2) - f1 (a, x2) = ∫ u in a..b, f11 (u, x2)) ∧
  (∀ x1 : ℝ, x1 ≤ 0 → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      IntervalIntegrable (fun u => f22 (x1, u)) volume a b ∧
        f2 (x1, b) - f2 (x1, a) = ∫ u in a..b, f22 (x1, u))

/-- `f_12` is the mixed second-order weak derivative of `f`: for every `x_1 ≤ 0`, the function
`f_1(x_1, ·)` is absolutely continuous on every compact interval of `[0, ∞)` with a.e.
derivative `f_12(x_1, ·)`, i.e. `f_1(x_1, b) − f_1(x_1, a) = ∫_a^b f_12(x_1, u) du` for
`0 ≤ a ≤ b`. -/
def HasWeakMixed (f1 f12 : ℝ × ℝ → ℝ) : Prop :=
  ∀ x1 : ℝ, x1 ≤ 0 → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    IntervalIntegrable (fun u => f12 (x1, u)) volume a b ∧
      f1 (x1, b) - f1 (x1, a) = ∫ u in a..b, f12 (x1, u)

/-- The fluid "generator" (3.4): `Lf(x) = (−x_1 + x_2 − β/√n) f_1(x) − x_2 f_2(x)`, written in
terms of the partial derivatives `f_1, f_2` of `f`. -/
noncomputable def Lop (β : ℝ) (n : ℕ) (f1 f2 : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (-x.1 + x.2 - β / Real.sqrt n) * f1 x - x.2 * f2 x

/-- The partial derivatives `f_1, f_2` of a function solve the PDE (3.7)–(3.8) (p. 8):
`Lf(x) = −((x_2 − κ/√n) ∨ 0)` for `x ∈ Ω`, and `f_1(0, x_2) = f_2(0, x_2)` for `x_2 ≥ 0`. -/
def SolvesPDE (β κ : ℝ) (n : ℕ) (f1 f2 : ℝ × ℝ → ℝ) : Prop :=
  (∀ x ∈ Omega, Lop β n f1 f2 x = -(max (x.2 - κ / Real.sqrt n) 0)) ∧
    ∀ x2 : ℝ, 0 ≤ x2 → f1 (0, x2) = f2 (0, x2)

/-- The second-order weak derivatives `f_11, f_12, f_22` satisfy the bounds (3.9)–(3.11) (p. 8):
`f_11, f_12, f_22 ≥ 0` on `Ω`; `f_11 = f_22 = 0` where `x_2 ∈ [0, κ/√n]`; and where `x_2 ≥ κ/√n`,
`f_11 ≤ (√n/β)(κ/(κ − β) + 1)` and `f_22 ≤ (√n/β)(5 + 2κ/(κ − β))`. -/
def DerivBounds (β κ : ℝ) (n : ℕ) (f11 f12 f22 : ℝ × ℝ → ℝ) : Prop :=
  (∀ x ∈ Omega, 0 ≤ f11 x ∧ 0 ≤ f12 x ∧ 0 ≤ f22 x) ∧
  (∀ x ∈ Omega, x.2 ≤ κ / Real.sqrt n → f11 x = 0 ∧ f22 x = 0) ∧
  (∀ x ∈ Omega, κ / Real.sqrt n ≤ x.2 →
      f11 x ≤ Real.sqrt n / β * (κ / (κ - β) + 1) ∧
        f22 x ≤ Real.sqrt n / β * (5 + 2 * κ / (κ - β)))

end JSQHalfinWhitt.Tightness


