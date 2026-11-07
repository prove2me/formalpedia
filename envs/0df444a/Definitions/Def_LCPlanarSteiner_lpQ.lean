-- Prove2me | Definitions.Def_LCPlanarSteiner_lpQ
-- name    : LCPlanarSteiner_lpQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:44.896575+00:00
-- url     : https://prove2.me/theorems/0e34d0e1-01da-4bdc-a3cd-2a35e9e438d4
-- title:
--   The parameters (14) of the total-budget LP
-- statement:
--   For a graph with $n$ vertices, an accuracy $\varepsilon$ and a bound $h$,
--   $$
--   L_0 = \Bigl(1 + \frac{\varepsilon}{4}\Bigr)h,\quad \Delta = \frac{\varepsilon h}{16 n},\quad q_e = \Bigl\lfloor \frac{\ell_e}{\Delta} \Bigr\rfloor,\quad Q = \Bigl\lfloor \frac{L_0}{\Delta} \Bigr\rfloor,\quad U = \Bigl(1 + \frac{\varepsilon}{2}\Bigr)h .
--   $$
--   $L_0$ is the junction horizon, $\Delta$ the level width, $q_e$ the rounded length of arc $e$, $Q$ the top level, and $U$ the bound on decomposed arm sums.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4.4, display (14), p.14

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **The parameters (14) of the total-budget LP.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4.4, display (14), p.14: "L₀ = (1 + ε/4)h, ∆ = εh/(16n), q_e = ⌊ℓ_e/∆⌋, Q = ⌊L₀/∆⌋,
U = (1 + ε/2)h."

`lpL0`, `lpDelta`, `lpQ`, `lpU` and `lpq G ε h e` are `L₀`, `∆`, `Q`, `U` and `q_e` for the graph `G`
(`n` its number of vertices), the accuracy `ε` and the length bound `h`.

**Formalization Note.** Floors are `Nat.floor` of nonnegative rationals. -/
def lpL0 (ε h : ℚ) : ℚ := (1 + ε / 4) * h

/-- `∆ = εh/(16n)`. -/
def lpDelta (G : Net) (ε h : ℚ) : ℚ := ε * h / (16 * G.n)

/-- `Q = ⌊L₀/∆⌋`, the top length level. -/
def lpQ (G : Net) (ε h : ℚ) : ℕ := ⌊lpL0 ε h / lpDelta G ε h⌋₊

/-- `q_e = ⌊ℓ_e/∆⌋`, the rounded length of arc `e`. -/
def lpq (G : Net) (ε h : ℚ) (e : ℕ) : ℕ := ⌊G.lng e / lpDelta G ε h⌋₊

/-- `U = (1 + ε/2)h`. -/
def lpU (ε h : ℚ) : ℚ := (1 + ε / 2) * h

end LCPlanarSteiner


