-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_LogLoss
-- name    : FoundationsML_MaxEnt_LogLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:15:36.071962+00:00
-- url     : https://prove2.me/theorems/5d22ff3c-3378-4013-84da-e81f682be69b
-- title:
--   Population log-loss of a Gibbs distribution
-- statement:
--   **§12.6, p. 303, PDF p. 320.** $L_D(w) = E_{x\sim D}[-\log p_w(x)]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, §12.6, p. 303 (PDF p. 320)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_GibbsDistribution

open MeasureTheory

namespace FoundationsML.MaxEnt

/-- The (population) log-loss `L_D(w)` of the Gibbs distribution `p_w` with respect to a
distribution `D` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, §12.6, p. 303, PDF p. 320): `L_D(w) = E_{x∼D}[−log p_w(x)]`. -/
noncomputable def LogLoss {X : Type*} [Fintype X] [MeasurableSpace X] {N : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (D : Measure X) (w : Fin N → ℝ) : ℝ :=
  ∫ x, -(Real.log (GibbsDistribution p0 Φ w x)) ∂D

end FoundationsML.MaxEnt


