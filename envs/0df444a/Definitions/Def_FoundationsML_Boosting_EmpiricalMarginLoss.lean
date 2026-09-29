-- Prove2me | Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
-- name    : FoundationsML_Boosting_EmpiricalMarginLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:58.781971+00:00
-- url     : https://prove2.me/theorems/e79e97b4-c095-4a3f-9dc3-0187dad86f3f
-- title:
--   Empirical margin loss (Definition 5.6, restated)
-- statement:
--   **Definition 5.6, p. 92, PDF p. 109 (restated locally for this chapter).**
--   $\hat R_{S,\rho}(h) = \frac1m\sum_{i=1}^m\Phi_\rho(y_ih(x_i))$.
--
--   **Formalization Note.** Byte-identical in structure to chunk `05-svm`'s own copy; restated
--   because a draft item cannot import another chunk's draft module.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 92, Definition 5.6 (PDF p. 109)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_PhiRho

namespace FoundationsML.Boosting

/-- The empirical margin loss of a real-valued hypothesis `h` on a sample `S = (x_1,…,x_m)`
with labels `y = (y_1,…,y_m)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 5.6, p. 92, PDF p. 109, restated locally for
this chapter): `R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(y_i h(x_i))`. -/
noncomputable def EmpiricalMarginLoss {X : Type*} {m : ℕ} (ρ : ℝ)
    (S : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, PhiRho ρ (y i * h (S i))

end FoundationsML.Boosting


