-- Prove2me | Definitions.Def_LL_Decomp587i_ZeroBelowOne
-- name    : LL_Decomp587i_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:36:39.258054+00:00
-- url     : https://prove2.me/theorems/c0d345d1-8aab-4e49-9724-9b80f6ce8c8f
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

namespace LL_Decomp587i

noncomputable section

open Real Set

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end

end LL_Decomp587i


