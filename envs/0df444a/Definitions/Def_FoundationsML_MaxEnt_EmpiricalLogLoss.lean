-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_EmpiricalLogLoss
-- name    : FoundationsML_MaxEnt_EmpiricalLogLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:16:13.470956+00:00
-- url     : https://prove2.me/theorems/65cc4eeb-7014-4477-953d-79c2f8cc00ee
-- title:
--   Empirical log-loss of a Gibbs distribution (optimization 12.12)
-- statement:
--   **§12.6, p. 303, PDF p. 320, and optimization (12.12), p. 302, PDF p. 319.**
--   $L_S(w) = \frac1m\sum_{i=1}^m -\log p_w(x_i)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 302-303 (PDF p. 319-320)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_GibbsDistribution

namespace FoundationsML.MaxEnt

/-- The empirical log-loss `L_S(w)` of the Gibbs distribution `p_w` with respect to a sample
`S` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press
2018, §12.6, p. 303, PDF p. 320, and the objective of optimization (12.12), p. 302, PDF p.
319): `L_S(w) = (1/m) ∑_{i=1}^m −log p_w(x_i)`. -/
noncomputable def EmpiricalLogLoss {X : Type*} [Fintype X] {N m : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (S : Fin m → X) (w : Fin N → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, -(Real.log (GibbsDistribution p0 Φ w (S i)))

end FoundationsML.MaxEnt


