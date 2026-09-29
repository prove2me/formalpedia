-- Prove2me | Definitions.Def_FoundationsML_Ranking_IsPDS
-- name    : FoundationsML_Ranking_IsPDS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:38:24.968341+00:00
-- url     : https://prove2.me/theorems/9f3c53c6-32c4-414c-83a9-0f88f86fd909
-- title:
--   Positive-definite symmetric (PDS) kernel
-- statement:
--   **Referenced p. 243, PDF p. 260.** $K:X\times X\to\mathbb R$ is PDS iff symmetric and
--   $\sum_{i,j} c_i c_j K(x_i,x_j)\ge0$ for every finite set of points and reals. Restated
--   locally since a draft cannot import chunk `06-kernels`'s own copy.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, referenced p. 243 (PDF p. 260)

import Mathlib

namespace FoundationsML.Ranking

/-- A positive-definite symmetric (PDS) kernel `K : X × X → ℝ` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, referenced at p. 243,
PDF p. 260, restated locally for this chapter since drafts cannot import chunk `06-kernels`'s
own draft copy): `K` is symmetric, and for every finite set of points `x_1,…,x_n ∈ X` and
reals `c_1,…,c_n`, `∑_{i,j} c_i c_j K(x_i,x_j) ≥ 0`. -/
def IsPDS {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y, K x y = K y x) ∧
    ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K (x i) (x j)

end FoundationsML.Ranking


