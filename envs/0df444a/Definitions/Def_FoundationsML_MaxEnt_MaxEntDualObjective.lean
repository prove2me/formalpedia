-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_MaxEntDualObjective
-- name    : FoundationsML_MaxEnt_MaxEntDualObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:14:49.994977+00:00
-- url     : https://prove2.me/theorems/07b8bee7-2392-4de9-8683-5bf0bc5254f1
-- title:
--   Maxent dual objective G (Eq. 12.10)
-- statement:
--   **Eq. (12.10), p. 300, PDF p. 317.** $G(w) = \frac1m\sum_{i=1}^m\log\frac{p_w(x_i)}
--   {p_0(x_i)} - \lambda\|w\|_1$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 300, Eq. (12.10) (PDF p. 317)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_GibbsDistribution

namespace FoundationsML.MaxEnt

/-- The Maxent dual objective `G` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Eq. (12.10), p. 300, PDF p. 317), for `w : Fin N → ℝ`:
`G(w) = (1/m) ∑_{i=1}^m log(p_w(x_i)/p0(x_i)) − λ‖w‖_1`. -/
noncomputable def MaxEntDualObjective {X : Type*} [Fintype X] {N m : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) (w : Fin N → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, Real.log (GibbsDistribution p0 Φ w (S i) / p0 (S i)) -
    lam * ∑ j, |w j|

end FoundationsML.MaxEnt


