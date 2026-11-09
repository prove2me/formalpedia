-- Prove2me | Definitions.Def_NadlerCLS_l1
-- name    : NadlerCLS_l1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:01.17778+00:00
-- url     : https://prove2.me/theorems/65f968f0-c531-45fd-85dd-edf38e78a0ec
-- title:
--   $\ell_1$ distance on $\mathbb R^n$ and real points of rational vectors
-- statement:
--   For $x, y \in \mathbb R^n$,
--   $$
--   \|x-y\|_1=\sum_{i=1}^{n}|x_i-y_i| .
--   $$
--   For a rational vector $x\in\mathbb Q^n$, $\bar x\in\mathbb R^n$ denotes the same point viewed as a real vector.
--
--   The paper uses the $\ell_1$ norm throughout its regularity conditions (Definitions 1, 2, 5 and Lemma C.1); answers of the search problems are rational points that the circuits evaluate as real points.
--
--   **Formalization Note** Mathlib's norm on $\mathbb R^n$ (`Fin n → ℝ`) is the sup norm, so the $\ell_1$ distance is written as this explicit sum. Coordinates are 0-based.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Section C.1, p.31 ("The norm is ℓ1 throughout"); Definitions 1, 2, p.9, p.11; Section 2, p.7

import Mathlib

set_option autoImplicit false

namespace NadlerCLS

/-- The **ℓ₁ distance** on `ℝⁿ` (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding
Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485; Definitions 1, 2 and 5, pp.9, 11, 31, and Section C.1, p.31: "The norm is ℓ1
throughout"):
`l1 x y = ∑ i, |x i - y i| = ‖x − y‖₁`.

**Formalization Note** Mathlib's `‖x - y‖` on `Fin n → ℝ` is the sup norm, so the ℓ₁ norm of
the paper is written as this explicit finite sum. Coordinates are 0-based (`Fin n`). -/
def l1 {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, |x i - y i|

/-- The **real point of a rational vector** (Xiong–Vlatakis-Gkaragkounis, arXiv:2609.14101, held
version of 2026-11-03, sha256 1fcc5a02…6dc485, Section 2, p.7: "all numerical parameters are
rational and represented in binary"): `rpt x i = (x i : ℝ)`. Answers of the search problems of
this mission are rational points, which the circuits evaluate as real points. -/
def rpt {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ := fun i => (x i : ℝ)

end NadlerCLS


