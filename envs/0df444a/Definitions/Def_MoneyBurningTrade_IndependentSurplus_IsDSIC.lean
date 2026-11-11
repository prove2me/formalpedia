-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
-- name    : MoneyBurningTrade_IndependentSurplus_IsDSIC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:22.922885+00:00
-- url     : https://prove2.me/theorems/457e1ad4-aff3-4292-9efe-ddac063c871b
-- title:
--   Definition 3.1 — dominant strategies in expectation
-- statement:
--   For a direct mechanism $M=(x,p_B,p_S)$ on a common report interval $T$, define buyer utility $u_b(b;r,t)=b x(r,t)-p_B(r,t)$ and seller utility $u_s(s;r,t)=p_S(r,t)+s(1-x(r,t))$. Dominant-strategy incentive compatibility means
--
--   $$u_b(b;r,b)\ge u_b(b;r,t),\qquad u_s(s;s,t)\ge u_s(s;r,t)$$
--
--   for every true value and report $s,r,b,t\in T$. These are utilities in expectation over internal mechanism randomness, separately at every report of the other trader. No expectation over the priors or condition on individual random seeds is imposed.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Definition 3.1, equations (1)–(2), printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Definition 3.1: pointwise dominant strategies in expectation over internal randomness.
Seller utility includes the value of retaining the good. All reports range over T. -/
def IsDSIC (T : Set ℝ) (M : SecondBestBT.Mechanism) : Prop :=
  (∀ b ∈ T, ∀ t ∈ T, ∀ r ∈ T,
    b * M.x (r, t) - M.pB (r, t) ≤ b * M.x (r, b) - M.pB (r, b)) ∧
  (∀ s ∈ T, ∀ r ∈ T, ∀ t ∈ T,
    M.pS (r, t) + s * (1 - M.x (r, t)) ≤
      M.pS (s, t) + s * (1 - M.x (s, t)))

end MoneyBurningTrade.IndependentSurplus


