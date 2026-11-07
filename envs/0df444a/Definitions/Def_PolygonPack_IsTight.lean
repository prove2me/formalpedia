-- Prove2me | Definitions.Def_PolygonPack_IsTight
-- name    : PolygonPack_IsTight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:49.375084+00:00
-- url     : https://prove2.me/theorems/5726d201-ed65-46b9-b952-0ed480efa78d
-- title:
--   The classes Large, Short, Slack, Tight, T⁺ and T⁰
-- statement:
--   For parameters $c,a_0>0$ the classes are
--   $$
--   \begin{aligned}
--   \mathrm{Large}&=\{P:\operatorname{area}(P)\ge a_0\},\\
--   \mathrm{Short}&=\{P:\operatorname{area}(P)<a_0,\ D(P)\le1\},\\
--   \mathrm{Slack}&=\{P:\operatorname{area}(P)<a_0,\ D(P)>1,\ h(P)\le c\,\delta(P)\},\\
--   \mathrm{Tight}&=\{P:\operatorname{area}(P)<a_0,\ D(P)>1,\ h(P)>c\,\delta(P)\},
--   \end{aligned}
--   $$
--   and $T^+$, $T^0$ are the Tight polygons with $d(P)>0$ and $d(P)\le0$. Every valid polygon lies in exactly one of Large, Short, Slack, $T^+$ and $T^0$.
--
--   The approximation algorithm treats $T^+\cup\mathrm{Slack}$, $\mathrm{Short}$ and $\mathrm{Large}\cup T^0$ separately.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2, p.5

import Mathlib
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_polyArea
import Definitions.Def_PolygonPack_canonBottom

namespace PolygonPack

/-- `Large = {P : area(P) ≥ a0}`. -/
def IsLarge (a0 : ℝ) (v : List (ℚ × ℚ)) : Prop := a0 ≤ polyArea v

/-- `Short = {P : area(P) < a0, D(P) ≤ 1}`. -/
def IsShort (a0 : ℝ) (v : List (ℚ × ℚ)) : Prop := polyArea v < a0 ∧ polyD v ≤ 1

/-- `Slack = {P : area(P) < a0, D(P) > 1, h(P) ≤ cδ(P)}`. -/
def IsSlack (c a0 : ℝ) (v : List (ℚ × ℚ)) : Prop :=
  polyArea v < a0 ∧ 1 < polyD v ∧ polyH v ≤ c * polyDelta v

/-- **The classes of the knapsack algorithm.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2, p.5: "Tight = {P : area(P) < a0, D(P) > 1,
h(P) > cδ(P)}", "T+ = {P ∈ Tight : d(P) > 0}, T0 = {P ∈ Tight : d(P) ≤ 0}", "J = Large ∪ T0".

**Formalization Note.** The thresholds are exactly the paper's, closed and strict as printed. `D`, `h`, `δ`
are read from the fixed diameter `diamPair`, and so is the canonical bottom `canonD`. `d` may be negative. -/
def IsTight (c a0 : ℝ) (v : List (ℚ × ℚ)) : Prop :=
  polyArea v < a0 ∧ 1 < polyD v ∧ c * polyDelta v < polyH v

/-- The canonical bottom `d(P)` for the polygon's fixed diameter. -/
noncomputable def canonD (v : List (ℚ × ℚ)) : ℝ := canonBottom v (diamPair v).1 (diamPair v).2

/-- `T+`, the positive-Tight class. -/
def IsTPlus (c a0 : ℝ) (v : List (ℚ × ℚ)) : Prop := IsTight c a0 v ∧ 0 < canonD v

/-- `T0`, the Tight polygons of nonpositive canonical bottom. -/
def IsTZero (c a0 : ℝ) (v : List (ℚ × ℚ)) : Prop := IsTight c a0 v ∧ canonD v ≤ 0

end PolygonPack


