-- Prove2me | Definitions.Def_AronszajnRK_SubspaceSum_sumProjection
-- name    : AronszajnRK_SubspaceSum_sumProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:49:33.227727+00:00
-- url     : https://prove2.me/theorems/0c995b38-4325-44a4-b910-f14661084994
-- title:
--   Projection onto the closed sum of two subspaces
-- statement:
--   Let $F_1$ and $F_2$ be closed linear subspaces of a complex Hilbert space $E$. Their algebraic sum is $F_1+F_2=\{f_1+f_2:f_i\in F_i\}$, and $F_1\oplus F_2$ denotes its closure. Define $P$ to be the orthogonal projection onto $F_1\oplus F_2$:
--
--   $$
--   P=\operatorname{proj}_{\overline{F_1+F_2}}.
--   $$
--
--   This projection is the target of the expansion in §12, Eq. (7). The algebraic sum need not be closed, so taking its closure is part of the definition.
--
--   **Formalization Note** Lean uses the join of two `ClosedSubmodule`s, which is the closure of their algebraic sum. The ambient space is an arbitrary complex Hilbert space; the paper applies this operator identity to an RKHS.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), pp. 375, 377, §12, definition of F₁⊕F₂

import Mathlib

namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, pp. 375, 377 (PDF pp. 39, 41). The projection onto the closed sum F₁ ⊕ F₂. -/
noncomputable def sumProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) : E →L[ℂ] E :=
  ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E).starProjection

end AronszajnRK.SubspaceSum


