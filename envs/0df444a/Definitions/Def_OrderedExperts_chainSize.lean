-- Prove2me | Definitions.Def_OrderedExperts_chainSize
-- name    : OrderedExperts_chainSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:38.708194+00:00
-- url     : https://prove2.me/theorems/09433f36-b6fa-4eec-930b-57a114326d0d
-- title:
--   Size $m_t$ of the active chain
-- statement:
--   The number $m_t=|X_t|$ of distinct actions recommended by the experts on round $t$; $m_t\le|\mathcal F|$.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 2.1, p.4

import Definitions.Def_OrderedExperts_active

namespace OrderedExperts

/-- **Size `mt` of the active chain.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 2.1, p.4: "`Xt = {at,f : f ∈ F}
= {xt,1 ≺ · · · ≺ xt,mt}`, `mt ≤ |F|`, be the distinct active actions at round `t`."

`chainSize rec t = mt` is the number of distinct recommended actions at round `t`. -/
def chainSize {A : Type*} [LinearOrder A] {n : ℕ} (rec : ℕ → Fin n → A) (t : ℕ) : ℕ :=
  (active rec t).card

end OrderedExperts


