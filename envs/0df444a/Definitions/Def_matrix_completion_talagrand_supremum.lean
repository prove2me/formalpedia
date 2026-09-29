-- Prove2me | Definitions.Def_matrix_completion_talagrand_supremum
-- name    : matrix_completion_talagrand_supremum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-25T04:19:02.948448+00:00
-- url     : https://prove2.me/theorems/5ce0b758-8099-409a-94b8-e0981d3373a6
-- statement:
--   This definition file introduces the explicit bilinear supremum used in Candes-Recht Appendix 9.1.
--
--   For a Bernoulli sample set $\Omega$, sampling rate $p$, and tangent projection $P_T$, the paper rewrites the tangent sampling deviation as a supremum over two Frobenius-unit test matrices.  In lecture-note notation, with
--   $$
--   y_{ij}=P_T(e_i e_j^\top),
--   $$
--   the supremum is
--   $$
--   \sup_{\|X_1\|_F,\|X_2\|_F\le1}
--   \sum_{i,j} (\delta_{ij}-p)\,p^{-1}
--   \langle X_1,y_{ij}\rangle\langle y_{ij},X_2\rangle.
--   $$
--   The Lean definition `tangentSamplingTalagrandSupremumDeviation` records this expression so that the probabilistic Talagrand theorem and the linear-algebra representation of the operator norm can be decomposed separately.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, the display rewriting $Z$ as a supremum before the bounded-increment and variance estimates.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand

/-!
Explicit bilinear supremum used in the Appendix 9.1 Talagrand argument.

The project definition `tangentSamplingDeviation` is an operator-norm supremum.
Appendix 9.1 rewrites the same random variable as a supremum of centered
coordinate sums indexed by two Frobenius-unit test matrices.  Keeping this
supremum as a separate definition lets the formal decomposition distinguish the
probabilistic Talagrand theorem from the linear-algebra representation step.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Appendix 9.1 bilinear supremum representation of the tangent sampling
deviation.

For each coordinate `(i,j)`, the coefficient is
`p⁻¹ * <X₁, P_T(eᵢeⱼᵀ)> * <P_T(eᵢeⱼᵀ), X₂>`.
The sampled centered sum is then maximized over Frobenius-unit test matrices
`X₁` and `X₂`. -/
noncomputable def tangentSamplingTalagrandSupremumDeviation
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real) : Real :=
  sSup {v : Real |
    ∃ X1 X2 : RealMatrix n1 n2,
      frobeniusNorm X1 ≤ 1 ∧ frobeniusNorm X2 ≤ 1 ∧
        v =
          ∑ i : Fin n1, ∑ j : Fin n2,
            (((if (i, j) ∈ Omega then (1 : Real) else 0) - p) *
              tangentSamplingTalagrandCoefficient S p X1 X2 i j)}

end MatrixCompletion


