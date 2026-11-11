-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
-- name    : MoneyBurningTrade_IndependentSurplus_IsWBB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:32.203246+00:00
-- url     : https://prove2.me/theorems/aea2fa69-6f89-4875-84bd-eb84c531dc50
-- title:
--   Definition 3.3 — pointwise weak budget balance
-- statement:
--   A mechanism is weakly budget balanced on $T$ when
--
--   $$p_B(s,b)\ge p_S(s,b)\qquad(s,b\in T).$$
--
--   The published strong-budget-balance predicate is reused separately. The auxiliary transfer-bounds predicate records the chain $0\le s x\le p_S\le p_B\le b x\le1$ on $[0,1]^2$. This chain is required as a theorem conclusion, derived from IR, WBB and allocation bounds, and is never an extra assumption on a competitor.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Definition 3.3 and equation (9), printed p. 14–15 (PDF p. 15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Definition 3.3: weak budget balance at every report profile, not ex ante. -/
def IsWBB (T : Set ℝ) (M : SecondBestBT.Mechanism) : Prop :=
  ∀ s ∈ T, ∀ b ∈ T, M.pS (s, b) ≤ M.pB (s, b)

/-- The bounded transfer chain (9), specialized to [0,1]. This is a conclusion,
not an extra admissibility assumption. -/
def TransferBounds (M : SecondBestBT.Mechanism) : Prop :=
  ∀ s ∈ reportInterval, ∀ b ∈ reportInterval,
    0 ≤ s * M.x (s, b) ∧ s * M.x (s, b) ≤ M.pS (s, b) ∧
    M.pS (s, b) ≤ M.pB (s, b) ∧ M.pB (s, b) ≤ b * M.x (s, b) ∧
    b * M.x (s, b) ≤ 1

end MoneyBurningTrade.IndependentSurplus


