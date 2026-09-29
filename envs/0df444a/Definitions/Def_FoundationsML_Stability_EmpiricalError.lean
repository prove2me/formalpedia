-- Prove2me | Definitions.Def_FoundationsML_Stability_EmpiricalError
-- name    : FoundationsML_Stability_EmpiricalError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:20:08.186585+00:00
-- url     : https://prove2.me/theorems/163e5d10-00ce-42b0-8afd-4572c444f86d
-- title:
--   Empirical error of a hypothesis on a sample
-- statement:
--   **Statement, p. 334, PDF p. 351.** The empirical error of $h$ on a sample
--   $S=(z_1,\dots,z_m)$ is $\hat R_S(h) = \frac1m\sum_{i=1}^m L_{z_i}(h)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 334 (PDF p. 351)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss

namespace FoundationsML.Stability

/-- The empirical error of a hypothesis `h` on a sample `S = (z_1, …, z_m)` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 334,
PDF p. 351): `R̂_S(h) = (1/m) ∑_{i=1}^m L_{z_i}(h)`. -/
noncomputable def EmpiricalError {X Y Y' : Type*} {m : ℕ} (L : Y' → Y → ℝ)
    (S : Fin m → X × Y) (h : X → Y') : ℝ :=
  (1 / (m : ℝ)) * ∑ i, Loss L h (S i)

end FoundationsML.Stability


