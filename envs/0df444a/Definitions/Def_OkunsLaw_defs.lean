-- Prove2me | Definitions.Def_OkunsLaw_defs
-- name    : OkunsLaw_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:29:39.359908+00:00
-- url     : https://prove2.me/theorems/b20abc0c-ac47-41c8-bfd5-a309c839756d
-- title:
--   Okun's law: annual change, growth rate, gap law
-- statement:
--   Basic vocabulary for Okun's law over discrete time (years $t\in\mathbb N$), for real-valued time series $x:\mathbb N\to\mathbb R$.
--
--   1. **Annual change.** $\Delta x_t = x_{t+1} - x_t$.
--   2. **Growth rate.** $g_x(t) = \dfrac{\Delta x_t}{x_t}$.
--   3. **Gap version of Okun's law in year $t$.** For actual output $Y$, potential GDP $\overline Y$, actual unemployment rate $u$, natural rate of unemployment $\overline u$, and coefficient $c\in\mathbb R$,
--   $$\frac{\overline Y_t - Y_t}{\overline Y_t} = c\,(u_t - \overline u_t).$$
--
--   These are the objects in which the gap version and the growth-rate version of Okun's law are stated.
--
--   **Formalization Note** Real division by zero returns $0$ in Lean, so theorems using these definitions carry explicit positivity hypotheses where needed.
-- source:
--   Wikipedia, "Okun's law", revision oldid=1341356066 (https://en.wikipedia.org/w/index.php?title=Okun%27s_law&oldid=1341356066), section "Mathematical statements" (gap version and the meanings of Y, Ybar, u, ubar, c, ΔY, Δu).

import Mathlib

/-!
# Okun's law — definitions

Platform definition file `Definitions.Def_OkunsLaw_defs` (draft).
Time is discrete (years `t : ℕ`); every economic quantity is a real-valued time series.
Source: Wikipedia, "Okun's law" (oldid 1341356066), sections "Mathematical statements"
and "Derivation of the growth rate form".
-/

namespace OkunsLaw

/-- Year-to-year change `Δx_t = x_{t+1} - x_t` of a time series. -/
def delta (x : ℕ → ℝ) (t : ℕ) : ℝ := x (t + 1) - x t

/-- Growth rate `Δx_t / x_t` of a time series from year `t` to year `t + 1`. -/
noncomputable def growthRate (x : ℕ → ℝ) (t : ℕ) : ℝ := delta x t / x t

/-- The gap version of Okun's law holds in year `t` with coefficient `c`:
`(Ȳ_t - Y_t) / Ȳ_t = c (u_t - ū_t)`, where `Y` is actual output, `Ybar` potential GDP,
`u` the actual unemployment rate and `ubar` the natural rate of unemployment. -/
def GapLaw (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ) : Prop :=
  (Ybar t - Y t) / Ybar t = c * (u t - ubar t)

end OkunsLaw


