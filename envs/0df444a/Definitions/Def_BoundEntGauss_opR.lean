-- Prove2me | Definitions.Def_BoundEntGauss_opR
-- name    : BoundEntGauss_opR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:05.430552+00:00
-- url     : https://prove2.me/theorems/2de06dec-9637-479a-8ddf-1d2d12a09a1d
-- title:
--   The skew-symmetric symmetry $R$ of Section IV
-- statement:
--   On the phase space $(x_1,p_1,x_2,p_2\mid x_3,p_3,x_4,p_4)$, $R$ is the skew-symmetric $8\times8$ matrix with
--
--   $$
--   R_{13}=R_{24}=R_{75}=R_{86}=1,\qquad R_{31}=R_{42}=R_{57}=R_{68}=-1,
--   $$
--
--   and all other entries zero. It exchanges the two modes on each side, quadrature by quadrature, satisfies $R^2=-\mathbb 1$, and commutes with the covariance matrix (9) and with the family (11).
--
--   **Formalization Note** "Zero remaining entries" is read together with skew symmetry, which fixes the four transposed entries to $-1$.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace BoundEntGauss

/-- **The skew-symmetric symmetry `R` of Section IV.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, p. 4 ("the skew symmetric operator R with R₁₃ = R₂₄ = R₇₅ = R₈₆ = 1, and zero
remaining entries").

On `(x₁, p₁, x₂, p₂ | x₃, p₃, x₄, p₄)`, `R` is skew-symmetric with `R₁₃ = R₂₄ = R₇₅ = R₈₆ = 1`
(hence `R₃₁ = R₄₂ = R₅₇ = R₆₈ = −1`) and all other entries zero. It exchanges the two modes of
each party, quadrature by quadrature.

**Formalization Note.** Coordinates as in `opS`. Alice's block sends `(0, k) ↦ (1, k)` with
entry `+1` at `((0,k),(1,k))` and `−1` at `((1,k),(0,k))`; Bob's block is its negative, giving
`R₇₅ = R₈₆ = 1`. "Zero remaining entries" refers to the entries not fixed by `R₁₃, R₂₄, R₇₅, R₈₆`
and skew symmetry. -/
def opR : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2) (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ :=
  Matrix.fromBlocks (fun p q => if p.2 = q.2 then !![0, 1; -1, 0] p.1 q.1 else 0) 0 0
    (fun p q => if p.2 = q.2 then !![0, -1; 1, 0] p.1 q.1 else 0)

end BoundEntGauss


