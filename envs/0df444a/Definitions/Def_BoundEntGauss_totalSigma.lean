-- Prove2me | Definitions.Def_BoundEntGauss_totalSigma
-- name    : BoundEntGauss_totalSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:36.257217+00:00
-- url     : https://prove2.me/theorems/4efd44c0-413c-48c9-94df-8f2d510057f0
-- title:
--   The symplectic matrix $\sigma=\sigma_A\oplus\sigma_B$
-- statement:
--   For a system of $n$ modes held by Alice and $m$ modes held by Bob, in canonical coordinates $(x_1,p_1,\dots,x_n,p_n\mid x_{n+1},p_{n+1},\dots)$, the **symplectic matrix** is the block-diagonal matrix
--
--   $$
--   \sigma=\sigma_A\oplus\sigma_B,\qquad \sigma_A=\bigoplus_{j=1}^{n}\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad \sigma_B=\bigoplus_{j=1}^{m}\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
--   $$
--
--   It governs the canonical commutation relations $i[R_\alpha,R_\beta]=\sigma_{\alpha\beta}\mathbb 1$ (Eq. (1)), and appears in the uncertainty condition $\gamma+i\sigma\ge0$.
--
--   **Formalization Note** Built from the published per-party `interleavedJ` ($J_{x_jp_j}=-1$, $J_{p_jx_j}=+1$).
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, Eq. (1) and p. 2 (symplectic direct sum)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (interleavedJ realCovarianceSum)

namespace BoundEntGauss

/-- **The symplectic matrix σ = σ_A ⊕ σ_B of a bipartite system.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 2 ("symplectic direct sum").

In canonical coordinates each mode contributes the block `[[0, −1], [1, 0]]` in the order
`(x, p)` (p. 2), and for a bipartite system `X = X_A ⊕ X_B` the symplectic matrix is block
diagonal, `σ = σ_A ⊕ σ_B`.

**Formalization Note.** `interleavedJ n` (published, `Intakenext100.P68`) has `J_{x_j p_j} = −1`
and `J_{p_j x_j} = +1`, which is the paper's `σ` for one party of `n` modes; the index is
`QuadratureIndex n = Fin n × Fin 2` with `(j, 0) = x_j`, `(j, 1) = p_j`. -/
def totalSigma (n m : ℕ) :
    Matrix (QuadratureIndex n ⊕ QuadratureIndex m) (QuadratureIndex n ⊕ QuadratureIndex m) ℝ :=
  realCovarianceSum (interleavedJ n) (interleavedJ m)

end BoundEntGauss


