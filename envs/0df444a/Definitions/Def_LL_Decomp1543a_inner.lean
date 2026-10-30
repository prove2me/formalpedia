-- Prove2me | Definitions.Def_LL_Decomp1543a_inner
-- name    : LL_Decomp1543a_inner
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:34:46.994788+00:00
-- url     : https://prove2.me/theorems/45bad988-4e1e-4e25-b7ed-4243fe974a22
-- title:
--   Inner weighted exponential sum
-- statement:
--   Define $I(c,N,U,\alpha,t)=\sum_{m\in\mathcal M(c,N,U,t)}a_m(U)e(\alpha mt)$ for real $c,U,\alpha$ and natural $N,t$.

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_mRange

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def inner (c : ℝ) (N : ℕ) (U α : ℝ) (t : ℕ) : ℂ :=
  ∑ m ∈ mRange c N U t, (am U m : ℂ) * e (α * ((m * t : ℕ) : ℝ))
end LL_Decomp1543a


