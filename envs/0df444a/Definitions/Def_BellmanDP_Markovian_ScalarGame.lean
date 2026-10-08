-- Prove2me | Definitions.Def_BellmanDP_Markovian_ScalarGame
-- name    : BellmanDP_Markovian_ScalarGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T21:35:35.634732+00:00
-- url     : https://prove2.me/theorems/11e78ee5-9147-44cc-ab97-135486a4ba02
-- title:
--   The scalar game equation $du/dt=\max_p\min_q[(Ap,q)-(Bp,q)u]$ and the ratio values $\max_p\min_q (Ap,q)/(Bp,q)$
-- statement:
--   Let $A$ and $B$ be real $m \times n$ matrices with $m, n \ge 1$, and let $p$ and $q$ range over the probability vectors of $\mathbb R^n$ and $\mathbb R^m$ (nonnegative entries summing to $1$). Write $(Ap, q) = \sum_{i=1}^m q_i (Ap)_i$.
--
--   1. The right-hand side of the scalar equation (13.2):
--   $$G(u) = \max_p \min_q \big[(Ap, q) - (Bp, q)\, u\big].$$
--   2. The two values of (13.3):
--   $$\max_p \min_q \frac{(Ap,q)}{(Bp,q)}, \qquad \min_q \max_p \frac{(Ap,q)}{(Bp,q)} .$$
--
--   These are the objects of Chapter XI, Theorem 5, which generalizes the extended min-max theorem of Chapter X.
--
--   **Formalization Note** Maxima and minima are written as real suprema and infima over the standard simplices. The simplices are compact and nonempty and the payoffs continuous (for the ratio, under $(Bp,q) \ge d > 0$), so they are attained and equal the book's Max and Min.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, § 13, Eqs. (13.1)-(13.3), p. 333

import Mathlib

namespace BellmanDP.Markovian

/-- Bellman, *Dynamic Programming*, Ch. XI, § 13, (13.1), p. 333: the bilinear form
`(Ap, q) = Σ_i q_i (Ap)_i` of an `m × n` matrix `A`, a vector `p ∈ ℝⁿ` and a vector `q ∈ ℝᵐ`. -/
def pairing {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ) : ℝ :=
  dotProduct q (A.mulVec p)

/-- Ch. XI, § 13, (13.2), p. 333: the right-hand side
`Max_p Min_q [(Ap, q) − (Bp, q) u]`, `p` and `q` ranging over probability vectors (the standard
simplices of `ℝⁿ` and `ℝᵐ`). Both simplices are compact and the payoff is continuous, so for
`m, n ≥ 1` the supremum and infimum are attained and are the book's `Max` and `Min`. -/
noncomputable def gameRHS {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (u : ℝ) : ℝ :=
  sSup ((fun p => sInf ((fun q => pairing A p q - pairing B p q * u) ''
    stdSimplex ℝ (Fin m))) '' stdSimplex ℝ (Fin n))

/-- Ch. XI, § 13, (13.3), p. 333: `Max_p Min_q (Ap, q)/(Bp, q)` over probability vectors. -/
noncomputable def maxMinRatio {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup ((fun p => sInf ((fun q => pairing A p q / pairing B p q) ''
    stdSimplex ℝ (Fin m))) '' stdSimplex ℝ (Fin n))

/-- Ch. XI, § 13, (13.3), p. 333: `Min_q Max_p (Ap, q)/(Bp, q)` over probability vectors. -/
noncomputable def minMaxRatio {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf ((fun q => sSup ((fun p => pairing A p q / pairing B p q) ''
    stdSimplex ℝ (Fin n))) '' stdSimplex ℝ (Fin m))

end BellmanDP.Markovian


