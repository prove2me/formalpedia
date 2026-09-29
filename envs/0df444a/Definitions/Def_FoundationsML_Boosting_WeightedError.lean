-- Prove2me | Definitions.Def_FoundationsML_Boosting_WeightedError
-- name    : FoundationsML_Boosting_WeightedError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:02:48.212648+00:00
-- url     : https://prove2.me/theorems/b7c612c4-749b-4b84-ad7d-d5c886de4a6e
-- title:
--   Distribution-weighted error of a base classifier
-- statement:
--   **§7.2, p. 147, PDF p. 164.** For a distribution $D$ over sample indices, a sample
--   $S=(x_1,\dots,x_m)$ with labels $y_1,\dots,y_m$, and a base classifier $h$, the
--   $D$-weighted error is $\varepsilon = \Pr_{i\sim D}[h(x_i)\ne y_i] =
--   \sum_{i=1}^m D(i)\,\mathbb 1_{h(x_i)\ne y_i}$: the quantity AdaBoost minimizes over $h\in H$
--   at each round, and evaluates at its own choice $h_t$ to get $\varepsilon_t$.
--
--   **Formalization Note.** This is the generic (any $D$, any $h$) weighted-error functional;
--   `AdaBoostEpsilon` instantiates it at AdaBoost's own $D_t$ and $h_t$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 147, §7.2 (PDF p. 164)

import Mathlib

namespace FoundationsML.Boosting

/-- The distribution-weighted error of a base classifier `h : X → ℝ` on a labeled sample
`(S, y)` under a weighting `D : Fin m → ℝ` over the sample indices (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, §7.2, p. 147, PDF p.
164): `ε = P_{i∼D}[h(x_i) ≠ y_i] = ∑_{i=1}^m D(i)·1_{h(x_i)≠y_i}`, the weight AdaBoost places
on `h`'s errors under `D`. -/
noncomputable def WeightedError {X : Type*} {m : ℕ}
    (D : Fin m → ℝ) (S : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  ∑ i, D i * (if h (S i) = y i then 0 else 1)

end FoundationsML.Boosting


