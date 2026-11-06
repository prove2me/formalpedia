-- Prove2me | Definitions.Def_InvMarketMaking_LOB_dkwConfig
-- name    : InvMarketMaking_LOB_dkwConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:08.996037+00:00
-- url     : https://prove2.me/theorems/7913cb70-7e10-4b7d-8687-a9c6373e233a
-- title:
--   DKW radius $\psi_t=\min\{1,\sqrt{\log(12T/\delta)/(2t)}\}$ and the instance of Algorithm 4 in Theorem 6.18
-- statement:
--   For a horizon $T$ and a confidence level $\delta$, the **DKW radius** is
--   $$
--   \psi_0=1,\qquad \psi_t(b,\delta)=\psi_t(a,\delta)=\min\Big\{1,\sqrt{\frac{\log(12T/\delta)}{2t}}\Big\}\quad(t\ge1),
--   $$
--   with the natural logarithm. The instance of Algorithm 4 used in Theorem 6.18 takes the grids $\mathcal B^\circ=\mathcal A^\circ=\{n/N:n=0,\dots,N\}$ of Eq. (22) with $N=\lceil\sqrt T\rceil$, and this radius for both bids and asks.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 6.18, p. 47, and Eq. (22), p. 46

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_grid
import Definitions.Def_InvMarketMaking_LOB_lobRound

namespace InvMarketMaking.LOB

/-- The DKW radius of Theorem 6.18 (Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 47):
`ψ_0 = 1` and `ψ_t(b, δ) = ψ_t(a, δ) = min{1, √(log(12T/δ)/(2t))}` for `t ≥ 1`. `log` is the
natural logarithm. -/
noncomputable def dkwRadius (T : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 else min 1 (Real.sqrt (Real.log (12 * T / δ) / (2 * t)))

/-- The instance of Algorithm 4 in Theorem 6.18 (p. 47): the grids `B° = A° = {n/N : n = 0, …, N}`
of Eq. (22) with `N = ⌈√T⌉`, and the deterministic radius `dkwRadius T δ` for bids and asks. -/
noncomputable def dkwConfig (Ω : Type*) (T : ℕ) (δ : ℝ) : LOBConfig Ω where
  Bg := grid ⌈Real.sqrt T⌉₊
  Ag := grid ⌈Real.sqrt T⌉₊
  ψF := fun t _ _ => dkwRadius T δ t
  ψS := fun t _ _ => dkwRadius T δ t

end InvMarketMaking.LOB


