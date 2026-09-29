-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_EmpiricalFeatureMean
-- name    : FoundationsML_MaxEnt_EmpiricalFeatureMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:13:03.289557+00:00
-- url     : https://prove2.me/theorems/d2ffc01f-a111-40c6-95d8-a49c03d16ece
-- title:
--   Empirical feature average
-- statement:
--   **Used from Eq. (12.5)-(12.6), p. 298, PDF p. 315.** $E_{x\sim\hat D}[\Phi(x)]_j =
--   \frac1m\sum_{i=1}^m\Phi(x_i)_j$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 298, Eq. (12.5)-(12.6) (PDF p. 315)

import Mathlib

namespace FoundationsML.MaxEnt

/-- The empirical average of the feature map `Φ` over a sample `S`, `E_{x∼D̂}[Φ(x)]` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, used from
Eq. (12.5)-(12.6), p. 298, PDF p. 315): `E_{x∼D̂}[Φ(x)]_j = (1/m) ∑_{i=1}^m Φ(x_i)_j`. -/
noncomputable def EmpiricalFeatureMean {X : Type*} {N m : ℕ}
    (Φ : X → Fin N → ℝ) (S : Fin m → X) : Fin N → ℝ :=
  fun j => (1 / (m : ℝ)) * ∑ i, Φ (S i) j

end FoundationsML.MaxEnt


