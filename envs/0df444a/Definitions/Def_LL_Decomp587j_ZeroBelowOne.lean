-- Prove2me | Definitions.Def_LL_Decomp587j_ZeroBelowOne
-- name    : LL_Decomp587j_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:16:04.447001+00:00
-- url     : https://prove2.me/theorems/ef273d12-59ab-478e-a820-1e9764ec0523
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

open Real Set

namespace LL_Decomp587j

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end LL_Decomp587j


