-- Prove2me | Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
-- name    : FoundationsML_Ranking_EmpiricalMarginLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:37:16.107986+00:00
-- url     : https://prove2.me/theorems/9ed13a9e-2752-403d-a26f-9c39d61278bd
-- title:
--   Empirical pairwise ranking margin loss (Eq. 10.3)
-- statement:
--   **Eq. (10.3), p. 241, PDF p. 258.** $\hat R_{S,\rho}(h) = \frac1m\sum_{i=1}^m
--   \Phi_\rho(y_i(h(x'_i)-h(x_i)))$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (10.3), p. 241 (PDF p. 258)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_MarginLossFunction

namespace FoundationsML.Ranking

/-- The empirical pairwise ranking margin loss of a scoring function `h : X → ℝ` on a sample
of pairs `(S1_i, S2_i)` with labels `y : Fin m → ℝ` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (10.3), p. 241, PDF p. 258):
`R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(y_i(h(x'_i) − h(x_i)))`. -/
noncomputable def EmpiricalMarginLoss {X : Type*} {m : ℕ}
    (ρ : ℝ) (S1 S2 : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, MarginLossFunction ρ (y i * (h (S2 i) - h (S1 i)))

end FoundationsML.Ranking


