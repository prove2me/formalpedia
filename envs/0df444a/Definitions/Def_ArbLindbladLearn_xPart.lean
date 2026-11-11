-- Prove2me | Definitions.Def_ArbLindbladLearn_xPart
-- name    : ArbLindbladLearn_xPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:32.944515+00:00
-- url     : https://prove2.me/theorems/fa27d75c-f673-4207-ae92-05c45b96ac9e
-- title:
--   The $x$- and $z$-parts of a Pauli label
-- statement:
--   For a Pauli label written in binary as $a=(z,x)\in\mathbb F_2^{2n}$, $x_i=1$ exactly when the $i$th letter is $X$ or $Y$, and $z_i=1$ exactly when it is $Z$ or $Y$.
--
--   These parts describe the displacement of a Pauli operator on the computational basis ($x$) and on the $X$ basis ($z$), used by the support-learning stage.
--
--   **Formalization Note** With letters $0=I,1=X,2=Y,3=Z$; $(-\mathrm i)ZX=Y$ gives the letter $Y$ for $(z_i,x_i)=(1,1)$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.2, p.12

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The `x`-part of a Pauli label (Definition 2.2, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.12): for
`a = (z, x)`, `xᵢ = 1` exactly when the `i`th letter is `X` or `Y`.

**Formalization Note** With letters `0 = I, 1 = X, 2 = Y, 3 = Z`, the paper's
`P_(z,x) = ⊗ᵢ (−i)^{zᵢxᵢ} Z^{zᵢ}X^{xᵢ}` has letter `X` for `(0,1)`, `Z` for `(1,0)`, and
`(−i)ZX = Y` for `(1,1)`. -/
def xPart {n : ℕ} (a : Pauli n) : Fin n → Bool := fun i => decide (a i = 1 ∨ a i = 2)

/-- The `z`-part of a Pauli label (Definition 2.2, p.12): `zᵢ = 1` exactly when the `i`th letter
is `Z` or `Y`. -/
def zPart {n : ℕ} (a : Pauli n) : Fin n → Bool := fun i => decide (a i = 3 ∨ a i = 2)

end ArbLindbladLearn


