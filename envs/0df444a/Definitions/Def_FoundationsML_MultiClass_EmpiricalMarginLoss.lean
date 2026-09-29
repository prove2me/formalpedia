-- Prove2me | Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
-- name    : FoundationsML_MultiClass_EmpiricalMarginLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:29:10.917826+00:00
-- url     : https://prove2.me/theorems/e6086270-a46d-4748-bc82-bac7653c7bd8
-- title:
--   Empirical multi-class margin loss (Eq. 9.5)
-- statement:
--   **Eq. (9.5), p. 215, PDF p. 232.** $\hat R_{S,\rho}(h) = \frac1m\sum_{i=1}^m
--   \Phi_\rho(\rho_h(x_i,y_i))$, the chapter's own multi-class margin loss (distinct from
--   chunk `05-svm`'s binary margin loss, though built from the same $\Phi_\rho$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (9.5), p. 215 (PDF p. 232)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_MarginFunction
import Definitions.Def_FoundationsML_MultiClass_MarginLossFunction

namespace FoundationsML.MultiClass

/-- The empirical margin loss of a multi-class scoring function `h : X × Y → ℝ` on a sample
`S : Fin m → X` against a target labeling function `f : X → Y` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (9.5), p. 215, PDF
p. 232): `R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(ρ_h(x_i,y_i))`. -/
noncomputable def EmpiricalMarginLoss {X Y : Type*} {m : ℕ}
    (ρ : ℝ) (S : Fin m → X) (f : X → Y) (h : X × Y → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, MarginLossFunction ρ (MarginFunction h (S i) (f (S i)))

end FoundationsML.MultiClass


