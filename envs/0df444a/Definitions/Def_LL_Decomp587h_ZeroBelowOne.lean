-- Prove2me | Definitions.Def_LL_Decomp587h_ZeroBelowOne
-- name    : LL_Decomp587h_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:08:06.8102+00:00
-- url     : https://prove2.me/theorems/4ad30884-cf4c-4db7-b94e-5a59b11f969f
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

open Real Set

namespace LL_Decomp587h

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end LL_Decomp587h


