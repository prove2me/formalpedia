-- Prove2me | Definitions.Def_LeblSCV_Levi_HasSmoothBoundary
-- name    : LeblSCV_Levi_HasSmoothBoundary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:38:41.702468+00:00
-- url     : https://prove2.me/theorems/19c1c3e5-f9fe-4096-b225-3006998d84ef
-- title:
--   Definition 2.2.1 — open set with smooth boundary
-- statement:
--   An open set $U \subset \mathbb{C}^n \cong \mathbb{R}^{2n}$ has **smooth boundary** if $\partial U$ is a smooth real hypersurface and at every $p \in \partial U$ there is a defining function $r$ with $r < 0$ for points in $U$ and $r > 0$ for points not in $\overline{U}$.
--
--   **Formalization Note.** `HasSmoothBoundary U` is `IsOpen U` together with, for each `p ∈ frontier U`, an open `V ∋ p` and `r` with `IsDefiningFunction U p V r`. The hypersurface condition on $\partial U$ is implied, because a defining function has nonvanishing derivative and cuts out $\partial U \cap V$. The sign condition (one side in $U$, the other outside) is part of the definition, as the book stresses on p. 54.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 54, Definition 2.2.1

import Mathlib
import Definitions.Def_LeblSCV_Levi_IsDefiningFunction

namespace LeblSCV.Levi

/-- Definition 2.2.1 (Lebl, p. 54), `k = ∞`: an open set `U ⊆ ℂⁿ` with smooth boundary has, at
every boundary point, a defining function negative on `U` and positive off `closure U`. -/
def HasSmoothBoundary {n : ℕ} (U : Set (Fin n → ℂ)) : Prop :=
  IsOpen U ∧ ∀ p ∈ frontier U, ∃ (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ),
    IsDefiningFunction U p V r

end LeblSCV.Levi


