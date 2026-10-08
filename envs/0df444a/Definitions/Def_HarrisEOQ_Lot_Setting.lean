-- Prove2me | Definitions.Def_HarrisEOQ_Lot_Setting
-- name    : HarrisEOQ_Lot_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:10.262237+00:00
-- url     : https://prove2.me/theorems/0d7b9070-7f66-42ac-8a53-1d145b7b42fb
-- title:
--   pp. 947–948 — stock level under regular movement, interest charge per piece, the cost per unit Y, the economic lot size √(240MS/C)
-- statement:
--   This file sets up the lot-size model of F. W. Harris (1913). A part is used at a regular rate of $M$ units per month; it costs $C$ dollars per unit (the quantity cost); each order carries a set-up cost of $S$ dollars; and it is made in lots of $X$ units. Interest and depreciation on stock are charged at ten per cent a year.
--
--   1. **Stock under regular movement.** Time $t \ge 0$ is measured in months from just after a delivery. A lot of $X$ arrives when the stock reaches nothing and is used at the constant rate $M$, so the stock is the sawtooth
--   $$
--   \operatorname{stock}(t) = X\bigl(1 - \{Mt/X\}\bigr),
--   $$
--   where $\{u\} = u - \lfloor u \rfloor$ is the fractional part. On the first cycle $0 \le t < X/M$ this is $X - Mt$; at $t = X/M$ the stock is replenished to $X$.
--
--   2. **Interest charge per piece**, built in Harris's own steps: the value of the average stock is $\tfrac12(CX + S)$ (set-up cost included); ten per cent of it is the annual charge; dividing by the $12M$ units used in a year gives
--   $$
--   \operatorname{interestPerPiece}(M, C, S, X) = \frac{\tfrac1{10}\cdot\tfrac12 (CX + S)}{12M}.
--   $$
--
--   3. **The whole cost of a unit**, the display $Y$ of p. 948, exactly as printed:
--   $$
--   Y(X) = \frac{1}{240M}(CX + S) + \frac{S}{X} + C .
--   $$
--
--   4. **The economic lot size**, the square root of $240MS$ divided by $C$:
--   $$
--   X^* = \sqrt{240MS/C}.
--   $$
--
--   These objects are shared by every statement of the mission: the average-stock and cost-per-unit milestones justify $Y$, and the goal theorem states that $X^*$ minimizes it.
--
--   **Formalization Note** All quantities are real numbers (the paper's own optimum for its stud example is $48.5$). The page uses the letter $I$ both for "the unit charge for interest and depreciation" and for $(1/240M)(CX+S)$; the Lean name is `interestPerPiece`. The definitions impose no sign conditions; theorems assume $M, C, S > 0$ and quantify over lot sizes $X > 0$. Lean's division by zero returns $0$ and `Real.sqrt` of a negative number returns $0$, so these definitions are only meaningful under those hypotheses.
-- source:
--   Harris, How many parts to make at once, Operations Research 38(6) (1990), pp. 947–948: the factors M, C, S, X (p. 947 right column to p. 948 left column), the ten per cent charge (p. 947 right column), the derivation and the display Y (p. 948 left column), and the square-root formula (p. 948 right column, top)

import Mathlib

namespace HarrisEOQ.Lot

/-- Stock on hand at time `t ≥ 0` (months, starting just after a delivery) under regular
movement: lots of `X` are delivered when the stock reaches nothing and used at the constant
rate `M` per month. It equals `X - M * t` on the first cycle `[0, X / M)`. -/
noncomputable def stockLevel (M X t : ℝ) : ℝ :=
  X * (1 - Int.fract (M * t / X))

/-- The interest and depreciation charge per piece, built as on p. 948: the value of the
average stock is `½ (C X + S)`, ten per cent of it is the annual charge, and it is divided by
the `12 M` units used in a year. -/
noncomputable def interestPerPiece (M C S X : ℝ) : ℝ :=
  (1 / 10) * ((1 / 2) * (C * X + S)) / (12 * M)

/-- The whole cost of a unit, the display `Y` of p. 948:
`(1 / 240M) (C X + S) + S / X + C`. -/
noncomputable def costPerUnit (M C S X : ℝ) : ℝ :=
  1 / (240 * M) * (C * X + S) + S / X + C

/-- The economic lot size: the square root of `240 M S` divided by `C`. -/
noncomputable def econLotSize (M C S : ℝ) : ℝ :=
  Real.sqrt (240 * M * S / C)

end HarrisEOQ.Lot


