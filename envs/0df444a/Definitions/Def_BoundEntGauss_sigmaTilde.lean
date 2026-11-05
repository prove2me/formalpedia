-- Prove2me | Definitions.Def_BoundEntGauss_sigmaTilde
-- name    : BoundEntGauss_sigmaTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:12.206939+00:00
-- url     : https://prove2.me/theorems/d6f45363-f744-4e29-94e8-c07e462666bb
-- title:
--   The partially transposed symplectic matrix $\tilde\sigma=(-\sigma_A)\oplus\sigma_B$
-- statement:
--   For an $n\times m$-mode bipartite system, the **partially transposed symplectic matrix** is
--
--   $$
--   \tilde\sigma=\begin{pmatrix}-\sigma_A&0\\0&\sigma_B\end{pmatrix},
--   $$
--
--   where $\sigma_A$, $\sigma_B$ are the symplectic matrices of Alice and Bob (blocks $\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ per mode). Reversing Alice's momenta changes the sign of her block, which is why the partial transpose of a state with covariance $\gamma$ leads to the condition $\gamma+i\tilde\sigma\ge0$ of Proposition 2.
--
--   **Formalization Note** The sign flip is on Alice (the first party), as printed in Eq. (7).
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Proposition 2, Eq. (7), p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (interleavedJ realCovarianceSum)

namespace BoundEntGauss

/-- **The partially transposed symplectic matrix σ̃ = (−σ_A) ⊕ σ_B.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Proposition 2, Eq. (7), p. 3.

`σ̃` is the symplectic matrix with Alice's block reversed in sign: `σ̃ = (−σ_A) ⊕ σ_B`, where
`σ_A`, `σ_B` are the per-party symplectic matrices with blocks `[[0, −1], [1, 0]]` per mode.

**Formalization Note.** As printed, the sign flip is on Alice (the first party, `Sum.inl`). The
published `Intakenext100.P68.partialTransposeCovariance` flips Bob's momenta instead and is not
used here. -/
def sigmaTilde (n m : ℕ) :
    Matrix (QuadratureIndex n ⊕ QuadratureIndex m) (QuadratureIndex n ⊕ QuadratureIndex m) ℝ :=
  realCovarianceSum (-(interleavedJ n)) (interleavedJ m)

end BoundEntGauss


