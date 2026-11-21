-- Prove2me | Definitions.Def_LL_Decomp587k_ZeroBelowOne
-- name    : LL_Decomp587k_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:42:18.620191+00:00
-- url     : https://prove2.me/theorems/59f4e770-2ce5-473b-ac10-b163dbf803bb
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

namespace LL_Decomp587k

noncomputable section

open Real Set

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end

end LL_Decomp587k


