-- Prove2me | Definitions.Def_BoundEntGauss_opC
-- name    : BoundEntGauss_opC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:07.290522+00:00
-- url     : https://prove2.me/theorems/906d4dbf-d19b-49dc-9a47-f5cf718fdb90
-- title:
--   The symmetry $C=\operatorname{diag}(1,-1,1,-1,1,-1,1,-1)$
-- statement:
--   On the phase space $(x_1,p_1,x_2,p_2\mid x_3,p_3,x_4,p_4)$ of the $2\times2$-mode system, $C$ is the multiplication operator
--
--   $$
--   C=\operatorname{diag}(1,-1,1,-1,1,-1,1,-1),
--   $$
--
--   equal to $+1$ on every position and $-1$ on every momentum coordinate. It commutes with the covariance matrix (9) and with the family (11).
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace BoundEntGauss

/-- **The symmetry `C` of Section IV.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, p. 4 ("the multiplication operator C with diagonal matrix elements
(1, −1, 1, −1, 1, −1, 1, −1)").

`C = diag(1, −1, 1, −1, 1, −1, 1, −1)` on `(x₁, p₁, x₂, p₂ | x₃, p₃, x₄, p₄)`: `+1` on every
position and `−1` on every momentum.

**Formalization Note.** Coordinates as in `opS`: `(j, 0)` is `x`, `(j, 1)` is `p`, Alice is
`Sum.inl`. -/
def opC : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2) (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ :=
  Matrix.diagonal (Sum.elim (fun p => !![1, -1; 1, -1] p.1 p.2) (fun p => !![1, -1; 1, -1] p.1 p.2))

end BoundEntGauss


