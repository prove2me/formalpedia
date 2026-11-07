-- Prove2me | Definitions.Def_PsdPermanent_RatInstance
-- name    : PsdPermanent_RatInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:47.600135+00:00
-- url     : https://prove2.me/theorems/a42f42c7-5e41-415f-99f1-43c6deb6f762
-- title:
--   A rational instance $(n,A,\varepsilon)$
-- statement:
--   An input of the algorithm consists of the dimension $n$, the real and imaginary parts of the entries of a matrix $A\in\mathbb C^{n\times n}$, all rational, and a rational accuracy parameter $\varepsilon$.
--
--   **Formalization Note** Validity is not bundled: an instance need not be Hermitian or positive semidefinite, and $\varepsilon$ may be nonpositive. Guarantees on the algorithm's output are stated only for valid instances.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 9, p.9

import Mathlib

namespace PsdPermanent

/-- **A rational instance of the algorithm.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 9, p.9: "For every ε > 0, there is a deterministic algorithm which, given a rational Hermitian
positive semidefinite matrix A ∈ C^{n×n}, runs in time polynomial in the input size, n, and log(1/ε)".

The dimension `n`, the real and imaginary parts of each entry of `A`, and the rational `eps`.

**Formalization Note.** `eps` is an input of one machine, since a time bound that names `log(1/ε)` makes
sense only that way. No validity is bundled: the machine runs on every instance, and its output is constrained
only when `0 < eps` and the matrix is positive semidefinite. -/
structure RatInstance where
  /-- the dimension -/
  n : ℕ
  /-- real parts of the entries -/
  re : Fin n → Fin n → ℚ
  /-- imaginary parts of the entries -/
  im : Fin n → Fin n → ℚ
  /-- the accuracy parameter -/
  eps : ℚ

/-- The complex matrix of a rational instance. -/
noncomputable def RatInstance.matrix (I : RatInstance) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  Matrix.of fun i j => ((I.re i j : ℚ) : ℂ) + ((I.im i j : ℚ) : ℂ) * Complex.I

end PsdPermanent


