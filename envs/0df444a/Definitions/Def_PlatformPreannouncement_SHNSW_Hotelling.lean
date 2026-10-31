-- Prove2me | Definitions.Def_PlatformPreannouncement_SHNSW_Hotelling
-- name    : PlatformPreannouncement_SHNSW_Hotelling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:17:34.991693+00:00
-- url     : https://prove2.me/theorems/3ec4172e-fce1-4ff5-9ce0-05c60404e1de
-- title:
--   Covered uniform Hotelling allocation with participation
-- statement:
--   A unit mass of agents is uniformly distributed on the real interval $[0,1]$. Two firms occupy its endpoints. For transport coefficient $t>0$ and location-independent utility components $v_0,v_1$, location $x$ yields utilities $v_0-tx$ and $v_1-t(1-x)$. A cutoff $q\in[0,1]$ assigns the left interval to firm 0 and the right interval to firm 1, with masses $q$ and $1-q$.
--
--   A covered allocation requires utility-maximizing adoption and nonnegative utility on each interval of positive mass. In cutoff form, when $q>0$, require $v_1-t(1-q)\le v_0-tq$ and $0\le v_0-tq$; when $q<1$, require the reverse comparison and $0\le v_1-t(1-q)$. Thus interior cutoffs satisfy indifference, while boundary cutoffs retain the appropriate weak inequalities. The isolated indifferent location has zero mass. These conditions are exactly the utility conditions throughout the corresponding intervals when $t>0$.
--
--   The predicate is defined algebraically for arbitrary real arguments; the economic application always supplies positive $t$. It contains no network effects, installed bases, tariff formulas, or equilibrium assumptions and can be used separately on each side of a two-sided market.
-- source:
--   Chellappa and Mukherjee (2020), DOI 10.1287/mnsc.2020.3606, held source.pdf pp. 10–11, 21–22, equation (12), pp. 25, 46–47 participation; boundary handling made explicit.

import Mathlib.Data.Real.Basic

namespace PlatformPreannouncement.SHNSW

/-- A covered unit uniform Hotelling market. The left firm's share is the
length `q` of its interval; the right firm's share is `1-q`. At an interior
cutoff the two weak choice inequalities force indifference. At an endpoint
only the firm serving a positive interval must satisfy participation/choice.
The isolated cutoff has zero mass. This object has no network-effect data. -/
def CoveredHotellingSplit (t v₀ v₁ q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧
  (0 < q → v₁ - t * (1 - q) ≤ v₀ - t * q ∧ 0 ≤ v₀ - t * q) ∧
  (q < 1 → v₀ - t * q ≤ v₁ - t * (1 - q) ∧ 0 ≤ v₁ - t * (1 - q))

end PlatformPreannouncement.SHNSW


