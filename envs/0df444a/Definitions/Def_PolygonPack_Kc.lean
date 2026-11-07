-- Prove2me | Definitions.Def_PolygonPack_Kc
-- name    : PolygonPack_Kc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:50.112359+00:00
-- url     : https://prove2.me/theorems/830ece83-a57a-421f-bed5-72590e016357
-- title:
--   Constants of the elongated geometry and the cutoffs
-- statement:
--   The constants of Appendices A and B are
--   $$
--   K=\frac2c+1,\quad L=\frac2c+6,\quad M=\frac{339}c+6,\quad B^*=\frac1{(1-2c)\bigl(1-2t_0/(1-2c)\bigr)^2},\quad B(D)=\frac{1-\gamma}{\sqrt2(1+\gamma)}.
--   $$
--   The **cutoff of Lemma A.5** is $h_0\le\min\{c/400,\ 1/(500K),\ 1/(300LK),\ 1/16\}$, and the **cutoff (11) of Lemma B.1** adds $h_0\le1/(82M)$.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.2, p.22; Lemma A.3, p.23; Lemma A.4, p.26; Lemma A.5, p.27; Lemma B.1, p.29

import Mathlib

namespace PolygonPack

/-- **Constants of the elongated geometry.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.2, p.22: "K = 2/c + 1, L = 2/c + 6", Lemma A.3,
p.23: "M = 339/c + 6", Lemma A.5, p.27: "B∗ = 1/((1 − 2c)(1 − 2t0/(1 − 2c))²)".

`bD D` is `B(D)` of (9), p.26. `IsA5Cutoff c h0` is the hypothesis `h0 ≤ min{c/400, 1/(500K), 1/(300LK), 1/16}` of
Lemma A.5. `IsB1Cutoff c h0` is (11), p.29. -/
noncomputable def Kc (c : ℝ) : ℝ := 2 / c + 1

/-- `L = 2/c + 6`. -/
noncomputable def Lc (c : ℝ) : ℝ := 2 / c + 6

/-- `M = 339/c + 6`. -/
noncomputable def Mc (c : ℝ) : ℝ := 339 / c + 6

/-- `B∗ = 1/((1 − 2c)(1 − 2t0/(1 − 2c))²)`. -/
noncomputable def bStar (c t0 : ℝ) : ℝ := 1 / ((1 - 2 * c) * (1 - 2 * t0 / (1 - 2 * c)) ^ 2)

/-- `B(D) = (1 − γ)/(√2(1 + γ))`, written with `γ` as an argument. -/
noncomputable def bD (γ : ℝ) : ℝ := (1 - γ) / (Real.sqrt 2 * (1 + γ))

/-- The cutoff hypothesis of Lemma A.5. -/
def IsA5Cutoff (c h0 : ℝ) : Prop :=
  h0 ≤ c / 400 ∧ h0 ≤ 1 / (500 * Kc c) ∧ h0 ≤ 1 / (300 * Lc c * Kc c) ∧ h0 ≤ 1 / 16

/-- The cutoff hypothesis (11) of Lemma B.1. -/
def IsB1Cutoff (c h0 : ℝ) : Prop := IsA5Cutoff c h0 ∧ h0 ≤ 1 / (82 * Mc c)

end PolygonPack


