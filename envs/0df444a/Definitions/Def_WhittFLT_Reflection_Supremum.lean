-- Prove2me | Definitions.Def_WhittFLT_Reflection_Supremum
-- name    : WhittFLT_Reflection_Supremum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:57.325685+00:00
-- url     : https://prove2.me/theorems/e2f07d59-eb9e-4e7d-b7ea-3b7d0e8341a4
-- title:
--   Running supremum, running infimum and the reflecting barrier
-- statement:
--   For a real-valued path $x$ on a time interval beginning at $0$, define its running supremum, running infimum, and reflecting barrier by
--
--   $$
--   x^{\uparrow}(t)=\sup_{0\le s\le t}x(s),\qquad x^{\downarrow}(t)=\inf_{0\le s\le t}x(s),\qquad f(x)(t)=x(t)-x^{\downarrow}(t).
--   $$
--
--   A path has no negative jumps when $x(t-)\le x(t)$ for each $t>0$ in the interval, and no positive jumps when $x(t)\le x(t-)$. These notions describe the jump conditions in the drift limits.
--
--   **Formalization Note** The real supremum and infimum are used only at times in the interval for càdlàg paths. Such paths are bounded on compact subintervals, so these are the ordinary finite extrema. The formula for $f$ subtracts the full running infimum, exactly as in the paper.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §6, pp. 80–81

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Reflection

open Set Filter Topology

/-- §6, p. 80: `x↑(t) = sup_{0 ≤ s ≤ t} x(s)`. -/
noncomputable def runSup (x : ℝ → ℝ) (t : ℝ) : ℝ := sSup (x '' Icc 0 t)

/-- §6, p. 81: `x↓(t) = inf_{0 ≤ s ≤ t} x(s)` (= −(−x)↑(t)). -/
noncomputable def runInf (x : ℝ → ℝ) (t : ℝ) : ℝ := sInf (x '' Icc 0 t)

/-- §6, p. 81: the impenetrable barrier at the origin, `f(x) = x − x↓`. -/
noncomputable def barrier (x : ℝ → ℝ) : ℝ → ℝ := fun t => x t - runInf x t

/-- `x` has no negative jump in `T`: `x(t−) ≤ x(t)` for `t ∈ T`, `t > 0`. -/
def NoNegJump (T : Set ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t ∈ T, 0 < t → Function.leftLim x t ≤ x t

/-- `x` has no positive jump in `T`: `x(t) ≤ x(t−)` for `t ∈ T`, `t > 0`. -/
def NoPosJump (T : Set ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t ∈ T, 0 < t → x t ≤ Function.leftLim x t

end WhittFLT.Reflection


