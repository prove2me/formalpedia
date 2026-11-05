-- Prove2me | Definitions.Def_DotySW_Deranged_Op
-- name    : DotySW_Deranged_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:22.69521+00:00
-- url     : https://prove2.me/theorems/47289eb9-1457-4d80-9e08-e10104c1af31
-- title:
--   Operators on a tensor space with $N$ positions, as matrices
-- statement:
--   The algebra $\mathrm{End}(V^{\otimes N})$ written as the algebra of square complex matrices indexed by the labels of `Idx`. It carries every operator of the mission: the group action $\rho$ and the diagram action $\sigma$.
--
--   **Formalization Note** Row index = output, column index = input, and an operator acts on a coordinate vector by matrix-vector multiplication.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, unnumbered, p. 9

import Mathlib
import Definitions.Def_DotySW_Deranged_Idx

namespace DotySW.Deranged

/-- **Operators on a tensor space with `N` positions.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, unnumbered, p. 9.

`Op n N` is the matrix algebra of `End(V^{⊗N})` in the basis `Idx n N`.

**Formalization Note** Row index = output, column index = input; operators act on coordinate
vectors by `Matrix.mulVec`. -/
abbrev Op (n N : ℕ) : Type := Matrix (Idx n N) (Idx n N) ℂ

end DotySW.Deranged


