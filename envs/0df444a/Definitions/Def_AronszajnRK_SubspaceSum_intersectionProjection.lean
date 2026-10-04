-- Prove2me | Definitions.Def_AronszajnRK_SubspaceSum_intersectionProjection
-- name    : AronszajnRK_SubspaceSum_intersectionProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:49:38.937552+00:00
-- url     : https://prove2.me/theorems/f4379b28-b387-47b2-b31d-847beb9951e5
-- title:
--   Projection onto the intersection of two subspaces
-- statement:
--   Let $F_1$ and $F_2$ be closed linear subspaces of a complex Hilbert space $E$. Put $F_0=F_1\cap F_2$ and define $P_0$ as its orthogonal projection:
--
--   $$
--   P_0=\operatorname{proj}_{F_1\cap F_2}.
--   $$
--
--   This is the limit of alternating projections and the constant term in the series for the projection onto the closed sum.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 376, §12, definition of F₀ and P₀

import Mathlib

namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, p. 376 (PDF p. 40). The projection P₀ onto F₁ ∩ F₂. -/
noncomputable def intersectionProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) : E →L[ℂ] E :=
  ((F₁ ⊓ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E).starProjection

end AronszajnRK.SubspaceSum


