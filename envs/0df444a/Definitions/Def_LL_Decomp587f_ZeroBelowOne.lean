-- Prove2me | Definitions.Def_LL_Decomp587f_ZeroBelowOne
-- name    : LL_Decomp587f_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:01:22.085921+00:00
-- url     : https://prove2.me/theorems/170f3f0f-9914-4d35-93cc-859d9d92b90c
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

open Real Set

namespace LL_Decomp587f

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end LL_Decomp587f


