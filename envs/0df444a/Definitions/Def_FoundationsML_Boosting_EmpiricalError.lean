-- Prove2me | Definitions.Def_FoundationsML_Boosting_EmpiricalError
-- name    : FoundationsML_Boosting_EmpiricalError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:07:11.258786+00:00
-- url     : https://prove2.me/theorems/ad99b200-78ff-49bd-8f2d-a5ee347a4335
-- title:
--   Empirical (zero-one) error of a real-valued function
-- statement:
--   **Proof of Theorem 7.2, p. 149, PDF p. 166.** For a real-valued function $f$ classified
--   through its sign, the empirical error is $\hat R_S(f) = \frac1m\sum_{i=1}^m
--   \mathbb 1_{y_if(x_i)\le 0}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 149, proof of Theorem 7.2 (PDF p. 166)

import Mathlib

namespace FoundationsML.Boosting

/-- The empirical (zero-one) error of a real-valued function `f : X → ℝ`, classified through
its sign against real-valued labels `y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, proof of Theorem 7.2, p. 149, PDF p. 166):
`R̂_S(f) = (1/m) ∑_{i=1}^m 1_{y_i f(x_i) ≤ 0}`. -/
noncomputable def EmpiricalError {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (f : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, (if y i * f (S i) ≤ 0 then (1 : ℝ) else 0)

end FoundationsML.Boosting


