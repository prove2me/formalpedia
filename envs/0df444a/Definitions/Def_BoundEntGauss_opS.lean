-- Prove2me | Definitions.Def_BoundEntGauss_opS
-- name    : BoundEntGauss_opS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:00.402387+00:00
-- url     : https://prove2.me/theorems/5772fba7-22c6-4882-890e-c4aecacba442
-- title:
--   The symmetry $S=\operatorname{diag}(1,1,-1,-1,1,-1,-1,1)$
-- statement:
--   On the phase space of two modes for Alice and two for Bob, with coordinates $(x_1,p_1,x_2,p_2\mid x_3,p_3,x_4,p_4)$, $S$ is the multiplication operator
--
--   $$
--   S=\operatorname{diag}(1,1,-1,-1,1,-1,-1,1).
--   $$
--
--   It is the most important symmetry of the example (9) and of the family (11): it satisfies $S\sigma+\tilde\sigma S=0$, and the covariance matrices of the family commute with it.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace BoundEntGauss

/-- **The symmetry `S` of Section IV.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, p. 4 ("the multiplication operator S with diagonal matrix elements
(1, 1, −1, −1, 1, −1, −1, 1)").

On the `2 × 2`-mode phase space with coordinates `(x₁, p₁, x₂, p₂ | x₃, p₃, x₄, p₄)`, `S` is the
diagonal matrix `diag(1, 1, −1, −1, 1, −1, −1, 1)`.

**Formalization Note.** Coordinates `1, …, 8` are `Sum.inl (0,0), Sum.inl (0,1), Sum.inl (1,0),
Sum.inl (1,1), Sum.inr (0,0), Sum.inr (0,1), Sum.inr (1,0), Sum.inr (1,1)`, where `(j, 0)` is
`x` and `(j, 1)` is `p` of the party's mode `j`; Alice is `Sum.inl`. The diagonal is written as
two `2 × 2` tables (mode, quadrature) for Alice and Bob. -/
def opS : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2) (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ :=
  Matrix.diagonal (Sum.elim (fun p => !![1, 1; -1, -1] p.1 p.2) (fun p => !![1, -1; -1, 1] p.1 p.2))

end BoundEntGauss


