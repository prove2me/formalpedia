-- Prove2me | Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_caseBDisplay
-- name    : LL_Decomp119LeavesIIS124CaseBRatio_caseBDisplay
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:45:45.624288+00:00
-- url     : https://prove2.me/theorems/6ba1c916-c155-41fd-99b1-03bd85de1647
-- title:
--   The case b display $D(x)$ of the minor arcs Type II estimate
-- statement:
--   The explicit real function $D(x)$ of the case b Type II bound on page 72 of Helfgott's minor arcs paper: with $y=x^{1/3}/6$ and $Q=x/U(x)$, it is the sum of four terms built from $x$, $y$, $Q$, $U(x)$, $V(x)$, $\mathfrak F(y)$, logarithms, square roots, powers $3/2$ and the constants $\kappa_2=1.93768$, $\kappa_6=0.60428$, $\kappa_7=0.1281$, $\kappa_9=3.9086$, exactly as written in the Lean definition.

import Mathlib
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_U
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_V
import Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_frakF

namespace LL_Decomp119LeavesIIS124CaseBRatio

noncomputable section

noncomputable def caseBDisplay (x : ℝ) : ℝ :=
  let y := x ^ ((1 : ℝ) / 3) / 6
  let Q := x / U x
  let κ2 : ℝ := 1.93768
  let κ6 : ℝ := 0.60428
  let κ7 : ℝ := 0.1281
  let κ9 : ℝ := 3.9086
  2 * x * Real.sqrt (frakF y) / Real.sqrt (8 * y) *
      Real.sqrt ((Real.log (x / (U x * Real.exp 2 * (8 * y))) +
          Real.log (3 * y) * Real.log (Real.log (x / (3 * U x * y)) /
            Real.log (8 * Real.exp 2 / 3))) *
        (κ6 * Real.log (x / (U x * Real.exp 2 * (2 * y))) + 2 * κ7)) +
    2 * κ2 / 3 * (x / Real.sqrt (16 * y) *
        (Real.log (8 * Real.exp 2 * y) ^ ((3 : ℝ) / 2) - Real.log y ^ ((3 : ℝ) / 2)) +
      x / 4 / Real.sqrt (Q - y) *
        (Real.log (Real.exp 2 * U x) ^ ((3 : ℝ) / 2) - Real.log y ^ ((3 : ℝ) / 2))) +
    (κ2 / Real.sqrt (2 * (1 - y / Q)) *
        (Real.sqrt (Real.log (V x)) + Real.sqrt (1 / Real.log (V x))) + κ9) *
      (x / Real.sqrt (V x)) +
    κ2 * Real.sqrt (2 * frakF y) *
      Real.sqrt (Real.log (Real.exp 2 * U x) / Real.log (8 * Real.exp 2 / 3)) *
      (x / Real.sqrt (U x))

end

end LL_Decomp119LeavesIIS124CaseBRatio


