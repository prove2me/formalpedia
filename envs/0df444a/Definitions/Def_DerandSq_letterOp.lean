-- Prove2me | Definitions.Def_DerandSq_letterOp
-- name    : DerandSq_letterOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:22.439864+00:00
-- url     : https://prove2.me/theorems/f46b5eed-ba70-4a8b-90b5-dbaa36c94095
-- title:
--   Letters $x_i, x_i^*$ evaluated at operators
-- statement:
--   A letter of a non-commutative $*$-polynomial in the variables $(x_i)_{i \in \iota}$ is either $x_i$ or $x_i^*$. Evaluated at a tuple $u = (u_i)_{i\in\iota}$ of bounded operators on a Hilbert space, $x_i \mapsto u_i$ and $x_i^* \mapsto u_i^*$ (the Hilbert-space adjoint).
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §2.4, p.12

import Mathlib

namespace DerandSq

/-- A letter `x_i` (`Sum.inl i`) or `x_i*` (`Sum.inr i`) of a ∗-polynomial evaluated at a tuple
`u` of bounded operators: `u_i`, resp. its adjoint `u_i*` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §2.4, p.12). -/
noncomputable def letterOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} (u : ι → E →L[ℂ] E) : ι ⊕ ι → E →L[ℂ] E
  | Sum.inl i => u i
  | Sum.inr i => star (u i)

end DerandSq


