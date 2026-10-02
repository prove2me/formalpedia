-- Prove2me | Definitions.Def_TeschlODE_IntervalMaps_SensitiveDependence
-- name    : TeschlODE_IntervalMaps_SensitiveDependence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:26:36.784191+00:00
-- url     : https://prove2.me/theorems/4ba591cc-bc70-4d51-888a-d984a005b501
-- title:
--   Sensitive dependence on initial conditions
-- statement:
--   A map $f : M \to M$ on a metric space $(M, d)$ exhibits **sensitive dependence on initial conditions** if there is a $\delta > 0$ such that for any $x \in M$ and any $\varepsilon > 0$ there are $y \in M$ and $n \in \mathbb{N} = \{1, 2, \dots\}$ with
--   $$d(x, y) < \varepsilon \quad\text{and}\quad d\bigl(f^n(x), f^n(y)\bigr) > \delta .$$
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 295–296, §11.3

import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.3, pp. 295–296: `f : M → M` exhibits sensitive dependence on initial conditions
if there is a `δ > 0` such that for any `x ∈ M` and any `ε > 0` there are a `y ∈ M` and an
`n ∈ ℕ = {1, 2, …}` with `d(x, y) < ε` and `d(fⁿ(x), fⁿ(y)) > δ`. -/
def SensitiveDependence {M : Type*} [MetricSpace M] (f : M → M) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : M, ∀ ε : ℝ, 0 < ε →
    ∃ y : M, ∃ n : ℕ, 1 ≤ n ∧ dist x y < ε ∧ δ < dist (f^[n] x) (f^[n] y)

end TeschlODE.IntervalMaps


