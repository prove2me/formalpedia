-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_Cond12
-- name    : GradSuffice_Thm8Data_Cond12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:24.89213+00:00
-- url     : https://prove2.me/theorems/b5efd8a9-c588-494d-a977-f5b0d7383747
-- title:
--   Condition (12)
-- statement:
--   A point $w$ satisfies **condition (12)** for indices $t\le D$ and $k\le\kappa$ if
--   $$|\eta_{u,k}\cdot y_k(w)|\le\frac{\theta}{128D}\,\mu_k(w)\qquad(t\le u\le D).$$
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7.2, p.21, Eq. (12)

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_eta
import Definitions.Def_GradSuffice_Thm8Data_mu

namespace GradSuffice

/-- **Condition (12).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7.2, p.21: for a point `w` and indices `t ≤ D`, `k ≤ κ`,
`|η_{u,k} · y_k(w)| ≤ (θ/(128D)) μ_k(w)` for `t ≤ u ≤ D`.

**Formalization Note.** 0-based `t`, `u`, `k`. -/
def Thm8Data.Cond12 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (t : Fin c.D) (k : Fin c.κ) (w : X) : Prop :=
  ∀ u : Fin c.D, t ≤ u → |c.eta u k (c.y k w)| ≤ c.θ / (128 * c.D) * c.mu k w

end GradSuffice


