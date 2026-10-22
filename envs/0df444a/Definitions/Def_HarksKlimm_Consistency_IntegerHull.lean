-- Prove2me | Definitions.Def_HarksKlimm_Consistency_IntegerHull
-- name    : HarksKlimm_Consistency_IntegerHull
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:07.236017+00:00
-- url     : https://prove2.me/theorems/c41001e8-8965-4838-aeba-de31c4616f01
-- title:
--   Finite integer linear hull with nonnegative offsets
-- statement:
--   For a class $C$ of cost functions, its finite integer linear hull with offsets is
--   $$\mathcal L_{\mathbb Z}(C)=\left\{x\mapsto\sum_{k=1}^K a_kc_k(x+b_k): K\in\mathbb N,\ a_k\in\mathbb Z,\ b_k\ge0,\ c_k\in C\right\}.$$
--   Functions and offsets may repeat. This hull is constructed from $C$ without any monotonicity filter.
--
--   **Formalization Note** `Fin K` indexes the finite sum; $K=0$ gives the zero function, even when $C$ is empty. Coefficients are integers cast to real scalars, and all arguments lie in the nonnegative half-line.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, §3, equation (3), p. 424 (PDF p. 6)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

def IntegerHull (C : Set (ℝ≥0 → ℝ)) : Set (ℝ≥0 → ℝ) :=
  {h | ∃ (K : ℕ) (a : Fin K → ℤ) (b : Fin K → ℝ≥0)
      (c : Fin K → ℝ≥0 → ℝ),
    (∀ k, c k ∈ C) ∧ ∀ x, h x = ∑ k : Fin K, (a k : ℝ) * c k (x + b k)}

end HarksKlimm.Consistency


