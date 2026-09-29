-- Prove2me | Definitions.Def_FoundationsML_MultiClass_IsPDS
-- name    : FoundationsML_MultiClass_IsPDS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:31:18.230394+00:00
-- url     : https://prove2.me/theorems/c115dc99-fe2b-43f7-a845-0a62e5eeb78c
-- title:
--   Positive-definite symmetric (PDS) kernel
-- statement:
--   **Referenced p. 219, PDF p. 236.** $K:X\times X\to\mathbb R$ is PDS iff symmetric and
--   $\sum_{i,j} c_i c_j K(x_i,x_j) \ge 0$ for every finite set of points and reals. Restated
--   locally since a draft cannot import chunk `06-kernels`'s own copy.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, referenced p. 219 (PDF p. 236)

import Mathlib

namespace FoundationsML.MultiClass

/-- A positive-definite symmetric (PDS) kernel `K : X × X → ℝ` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, referenced at p. 219,
PDF p. 236, restated locally for this chapter since drafts cannot import chunk `06-kernels`'s
own draft copy): `K` is symmetric, and for every finite set of points `x_1,…,x_n ∈ X` and
reals `c_1,…,c_n`, `∑_{i,j} c_i c_j K(x_i,x_j) ≥ 0`. -/
def IsPDS {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y, K x y = K y x) ∧
    ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K (x i) (x j)

end FoundationsML.MultiClass


