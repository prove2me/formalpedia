-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
-- name    : MoneyBurningTrade_IndependentSurplus_IsIR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:29.912452+00:00
-- url     : https://prove2.me/theorems/6e454cfc-4620-43f0-945e-62928ab8430c
-- title:
--   Definition 3.2 — pointwise individual rationality
-- statement:
--   For each truthful profile $(s,b)\in T^2$, individual rationality requires both traders to receive at least their no-trade utility:
--
--   $$b x(s,b)-p_B(s,b)\ge0,\qquad p_S(s,b)-s x(s,b)\ge0.$$
--
--   The second expression subtracts the seller's outside option, retaining an item of value $s$. These conditions concern expected transfers and allocation at each profile, without averaging over either prior.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Definition 3.2, equations (5)–(6), printed p. 14 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Definition 3.2: participation at every profile, relative to no trade. -/
def IsIR (T : Set ℝ) (M : SecondBestBT.Mechanism) : Prop :=
  ∀ s ∈ T, ∀ b ∈ T,
    0 ≤ b * M.x (s, b) - M.pB (s, b) ∧
    0 ≤ M.pS (s, b) - s * M.x (s, b)

end MoneyBurningTrade.IndependentSurplus


