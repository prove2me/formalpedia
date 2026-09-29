-- Prove2me | Definitions.Def_FoundationsML_DimReduction_SqNorm
-- name    : FoundationsML_DimReduction_SqNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:27:18.988982+00:00
-- url     : https://prove2.me/theorems/cf0f364f-ce5b-4129-867c-da1a5dff7477
-- title:
--   Squared Euclidean norm (coordinate-wise)
-- statement:
--   **§15.4, used throughout Lemmas 15.3-15.4, p. 354-355, PDF p. 371-372.** For
--   $v\in\mathbb R^n$, $\|v\|^2 = \sum_{i=1}^nv_i^2$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, §15.4, p. 354-355 (PDF p. 371-372)

import Mathlib

namespace FoundationsML.DimReduction

/-- The squared Euclidean norm `‖v‖²` of a vector `v ∈ ℝⁿ`, written coordinate-wise as a sum of
squares (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press
2018, §15.4, used throughout Lemmas 15.3-15.4, p. 354-355, PDF p. 371-372, e.g. `‖u−v‖²`,
`‖f(u)−f(v)‖²`): `‖v‖² = ∑_{i=1}^n v_i²`. -/
def SqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2

end FoundationsML.DimReduction


