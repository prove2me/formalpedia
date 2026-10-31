-- Prove2me | Definitions.Def_ShapleyNV_nvCost
-- name    : ShapleyNV_nvCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:03.933195+00:00
-- url     : https://prove2.me/theorems/0f21eedb-71a8-4f98-aca2-d754536f2de3
-- title:
--   Newsvendor cost $\Psi(y,z) = h(y-z)^+ + b(z-y)^+$
-- statement:
--   A company orders a quantity $y$ of a perishable product before the demand $z$ is observed. With unit holding cost $h$ and unit backorder cost $b$, the total cost is
--
--   $$
--   \Psi(y, z) := h\,(y-z)^+ + b\,(z-y)^+ ,
--   $$
--
--   where $a^+ = \max(a, 0)$.
--
--   This is the loss of every problem in the mission: the robust problems (P) and $(\widehat{\mathrm P})$ average it over a worst-case distribution of features and demands.
--
--   **Formalization Note** The function is defined for all real $y, z$. The standing assumption $b>0$, $0\le h\le b$ of the paper is a hypothesis of the theorems.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §2.1, display defining Ψ, p.4

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Newsvendor cost** `Ψ(y, z) := h (y − z)⁺ + b (z − y)⁺`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §2.1, display defining Ψ, p.4: the total cost of ordering `y` when the demand is `z`,
with unit holding cost `h` and unit backorder cost `b`.

**Formalization Note.** `a⁺` is `max a 0`. The function is defined for all real `y, z`; the paper
uses it for `y, z ∈ 𝒵 = ℝ₊`. The standing assumption `b > 0`, `0 ≤ h ≤ b` (p.6) is a hypothesis
of the theorems, not of this definition. -/
def nvCost (h b y z : ℝ) : ℝ := h * max (y - z) 0 + b * max (z - y) 0

end ShapleyNV


