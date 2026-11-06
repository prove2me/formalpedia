-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_y
-- name    : GradSuffice_Thm8Data_y
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:50.3852+00:00
-- url     : https://prove2.me/theorems/9c96e528-8fa2-4cdc-95e3-ee5f1aa7e310
-- title:
--   Rescaled points $y_k(w)$
-- statement:
--   The construction of Theorem 8 rescales the query point around the witnesses: $y_1(w)=w$ and
--   $$y_{k+1}(w):=\frac{y_k(w)-(1-r)\,w_{\sigma_k}}{r},\qquad r=\theta/256 .$$
--
--   **Formalization Note** 0-based: $y_0(w)=w$; values for indices $\ge\kappa$ are never used.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.18

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data
import Definitions.Def_GradSuffice_thm8R

namespace GradSuffice

/-- **The rescaled points `y_k(w)`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.18: "`y₁(w) = w` and
`y_{k+1}(w) := (y_k(w) − (1 − r) w_{σ_k}) / r`".

**Formalization Note.** 0-based: `y 0 w = w` and `y (k+1) w = r⁻¹ (y k w − (1 − r) w_{σ_k})` for
`k < κ`; the values for `k ≥ κ` are never used. -/
noncomputable def Thm8Data.y {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) : ℕ → X → X
  | 0, w => w
  | k + 1, w =>
    if h : k < c.κ then (thm8R c.θ)⁻¹ • (c.y k w - (1 - thm8R c.θ) • c.wσ ⟨k, h⟩) else c.y k w

end GradSuffice


