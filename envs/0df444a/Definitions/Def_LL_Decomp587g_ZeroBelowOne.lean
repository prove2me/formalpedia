-- Prove2me | Definitions.Def_LL_Decomp587g_ZeroBelowOne
-- name    : LL_Decomp587g_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T00:58:05.270954+00:00
-- url     : https://prove2.me/theorems/7e842c28-8b4e-474c-9d05-1bdd373cf7cc
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

open Real Set

namespace LL_Decomp587g

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end LL_Decomp587g


