-- Prove2me | Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss
-- name    : FoundationsML_SVM_EmpiricalMarginLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:26:28.935234+00:00
-- url     : https://prove2.me/theorems/5e8dc1f5-3901-400b-abf1-96350101624a
-- title:
--   Empirical margin loss (Definition 5.6)
-- statement:
--   **Definition 5.6 (Empirical margin loss), p. 92, PDF p. 109.** Given a sample
--   $S=(x_1,\dots,x_m)$ with labels $y_1,\dots,y_m$ and a hypothesis $h$, the empirical margin
--   loss is $\hat R_{S,\rho}(h) = \frac1m\sum_{i=1}^m \Phi_\rho(y_i h(x_i))$.
--
--   **Formalization Note.** `EmpiricalMarginLoss ρ S y h` takes the sample points and labels as
--   separate functions `S y : Fin m → …` rather than a single sample of pairs, matching how the
--   quantity is used in the goal theorem (where `S` ranges over `Fin m → X × ℝ` and is split via
--   `.1`/`.2`).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 92, Definition 5.6 (PDF p. 109)

import Mathlib
import Definitions.Def_FoundationsML_SVM_PhiRho

namespace FoundationsML.SVM

/-- The empirical margin loss of a real-valued hypothesis `h` on a sample
`S = (x_1, …, x_m)` with labels `y = (y_1, …, y_m)` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 5.6, p. 92, PDF p. 109):
`R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(y_i h(x_i))`. -/
noncomputable def EmpiricalMarginLoss {X : Type*} {m : ℕ} (ρ : ℝ)
    (S : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, PhiRho ρ (y i * h (S i))

end FoundationsML.SVM


