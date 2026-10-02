-- Prove2me | Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint
-- name    : TeschlQM_Shared_IsEssentiallySelfAdjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:55.784981+00:00
-- url     : https://prove2.me/theorems/19c54880-1b02-4c37-9e52-8cd7db442073
-- title:
--   Essentially self-adjoint operator
-- statement:
--   A (closable) operator $A$ is **essentially self-adjoint** if its closure $\overline{A}$, the operator whose graph is the closure of the graph of $A$ in $\mathfrak{H} \times \mathfrak{H}$, is self-adjoint:
--   $$\overline{A}^{\,*} = \overline{A}.$$
--   In this case $\mathfrak{D}(A)$ is called a core for $\overline{A}$, and $\overline{A}$ is the only self-adjoint extension of $A$.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `01-self-adjoint`: p. 66, Lemma 2.7
--   - chunk `06-kato-rellich`: p. 135, Theorem 6.4, Eq. (6.3)
--
--   **Formalization Note.** The closure is Mathlib's `LinearPMap.closure` (equal to `A` itself when `A` is not closable, a case that never arises for symmetric `A`). Self-adjointness is Mathlib's `IsSelfAdjoint` for `LinearPMap`, i.e. equality with the adjoint; it implies a dense domain.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 63, Section 2.2

import Mathlib

namespace TeschlQM.Shared

/-- Teschl, p. 63: `A` is *essentially self-adjoint* if its closure `Ā` is self-adjoint.
`LinearPMap.closure` is the operator whose graph is the closure of the graph of `A` (for a closable
`A`); self-adjointness is Mathlib's `IsSelfAdjoint`, i.e. `Ā† = Ā`. -/
def IsEssentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) : Prop :=
  IsSelfAdjoint A.closure

end TeschlQM.Shared


