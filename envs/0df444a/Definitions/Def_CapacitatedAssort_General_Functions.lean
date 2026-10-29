-- Prove2me | Definitions.Def_CapacitatedAssort_General_Functions
-- name    : CapacitatedAssort_General_Functions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:18.071337+00:00
-- url     : https://prove2.me/theorems/dd33028a-e381-4e8a-9019-2d4ce1597c59
-- title:
--   Coordinate monotonicity and uniform scaling stability
-- statement:
--   For a function $g:\mathbb R^M\to\mathbb R$ and an increasing block of size $k$, mixed monotonicity means nondecreasing dependence on each of the first $k$ coordinates and nonincreasing dependence on the rest, with other coordinates fixed, on the entire real domain. The scale map multiplies the first block by $\alpha$ and the remaining block by $\beta$.
--
--   A small error is an everywhere nonnegative real function $u$ for which there are $C\ge0$ and $\eta>0$ such that $u(\delta)\le C\delta$ for $0<\delta<\eta$. Scaling stability requires that for every two such errors $u,v$, there is a small error $e$ and a positive threshold, uniform over all $x\in\mathbb R^M$, for which
--   $$g(\operatorname{scale}(1-u(\delta),1+v(\delta),x))\ge(1-e(\delta))g(x).$$
--   This is the declared uniform reading of Assumption 2. Zero error is allowed, so negative constant functions are not excluded. These function properties are independent of the assortment model. No continuity, nonnegativity or computability requirement is imposed on $g$. Definitions are total also at zero dimension; source theorems require positive dimension and $k\le M$.
-- source:
--   Désir, Goyal and Zhang (2021), Technical Note—Capacitated Assortment Optimization: Hardness and Approximation, https://doi.org/10.1287/opre.2021.2142, held source.pdf, Assumptions 1–2, PDF/printed pp. 10–11

import Mathlib

namespace CapacitatedAssort.General

/-- Componentwise monotonicity on the entire real domain, with a fixed split. -/
def MixedMonotone {M : ℕ} (k : ℕ) (g : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ (m : Fin M) (x : Fin M → ℝ) (s t : ℝ), s ≤ t →
    if m.val < k then g (Function.update x m s) ≤ g (Function.update x m t)
    else g (Function.update x m t) ≤ g (Function.update x m s)

/-- Nonnegative O(δ) error near zero from the right; zero error is permitted. -/
def SmallError (u : ℝ → ℝ) : Prop :=
  (∀ δ, 0 ≤ u δ) ∧ ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧
    ∀ δ, 0 < δ → δ < η → u δ ≤ C * δ

def scale {M : ℕ} (k : ℕ) (α β : ℝ) (x : Fin M → ℝ) : Fin M → ℝ :=
  fun m => (if m.val < k then α else β) * x m

/-- Uniform reading of Assumption 2: the loss and threshold precede all x. -/
def ScalingStable {M : ℕ} (k : ℕ) (g : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ u v : ℝ → ℝ, SmallError u → SmallError v →
    ∃ e : ℝ → ℝ, SmallError e ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ, 0 < δ → δ < η → ∀ x : Fin M → ℝ,
        (1 - e δ) * g x ≤ g (scale k (1 - u δ) (1 + v δ) x)

end CapacitatedAssort.General


