-- Prove2me | Definitions.Def_SolarNonOwn_BizChoice_Utility
-- name    : SolarNonOwn_BizChoice_Utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:15:47.109392+00:00
-- url     : https://prove2.me/theorems/891ae34b-9656-4bf7-97ff-842b492f54ad
-- title:
--   §3.1, p. 7 — quadratic gross utility
-- statement:
--   A customer with demand satiation level $\delta$ obtains gross utility from monthly electricity usage $q$ according to
--
--   $$V(q\mid\delta)=\delta q-\frac{q^2}{2}. $$
--
--   This concave quadratic is the primitive used in Lemma 1 to determine electricity usage under each business model.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. 7, §3.1

import Mathlib

noncomputable section

namespace SolarNonOwn.BizChoice

/-- Gross utility from consuming `q` at satiation level `δ` (§3.1, p. 7). -/
def grossUtility (q δ : ℝ) : ℝ := δ * q - q ^ 2 / 2

end SolarNonOwn.BizChoice


