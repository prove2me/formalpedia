-- Prove2me | Definitions.Def_matrix_completion_talagrand_tangent_bilinear
-- name    : matrix_completion_talagrand_tangent_bilinear
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-25T04:39:56.265698+00:00
-- url     : https://prove2.me/theorems/cbeb9729-b5ae-4ff1-b5e6-ca5caf973386
-- statement:
--   This definition introduces the tangent-restricted bilinear supremum used as an intermediate step in the Appendix 9.1 representation of the tangent sampling deviation.
--
--   Let $p$ be the Bernoulli sampling rate and let $P_T$ be the tangent-space projection at the rank-$r$ matrix.  The usual tangent sampling deviation is
--   $$
--   Z(\Omega)=\sup_{X\in T,\ \|X\|_F\le1}
--   p^{-1}\|P_TP_\Omega X-pX\|_F.
--   $$
--   After applying Frobenius duality to the norm, the same operator is tested against another Frobenius-unit matrix $X_1$, giving the intermediate expression
--   $$
--   \sup_{\|X_1\|_F\le1,\ X_2\in T,\ \|X_2\|_F\le1}
--   p^{-1}\left\langle X_1, P_TP_\Omega X_2-pX_2\right\rangle_F.
--   $$
--   The Lean definition `tangentSamplingTangentBilinearDeviation` records this intermediate expression.  It is useful because the next representation lemma can expand this bilinear form in the coordinate basis and identify it with the unrestricted Appendix 9.1 supremum.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is rewritten from an operator norm into a supremum over two test matrices.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_supremum

/-!
Intermediate bilinear form for the Appendix 9.1 representation of the tangent
sampling deviation.

The already-uploaded `matrix_completion_talagrand_supremum` definition stores
the unrestricted coordinate supremum from Appendix 9.1.  This companion
definition stores the intermediate expression obtained directly from the
operator-norm definition by Frobenius duality, before the coordinate expansion
removes the tangent restriction from the second test matrix.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Tangent-restricted bilinear form of the tangent sampling fluctuation.

This is the intermediate expression obtained by applying Frobenius duality to
the norm in `tangentSamplingDeviation`, before expanding the sampling operator
in the coordinate basis and removing the tangent-space restriction from the
second test matrix. -/
noncomputable def tangentSamplingTangentBilinearDeviation
    {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : Real) : Real :=
  sSup {v : Real |
    ∃ X1 X2 : RealMatrix n1 n2,
      frobeniusNorm X1 ≤ 1 ∧
        tangentProjection S X2 = X2 ∧
          frobeniusNorm X2 ≤ 1 ∧
            v =
              p⁻¹ *
                matrixInner X1
                  (tangentProjection S (samplingProjection Omega X2) - p • X2)}

end MatrixCompletion


