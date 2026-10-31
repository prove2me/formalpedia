-- Prove2me | Definitions.Def_StrategyproofMultidim_util
-- name    : StrategyproofMultidim_util
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:25.231528+00:00
-- url     : https://prove2.me/theorems/40f86fb5-9d94-4d84-b2bc-eaaa79c15331
-- title:
--   Quasilinear utility $u(\mu_i(w);x)$
-- statement:
--   For a mechanism $\mu=(d,p)$, a reported profile $w$, a buyer $i$ and a valuation vector $x$,
--   $$u(\mu_i(w);x)=d_i(w)^{\top}x-p_i(w)$$
--   is the utility of buyer $i$, whose true valuation is $x$, from the bundle and the price the mechanism assigns to $i$ at the report $w$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.5 (PDF p.6); Definitions 1 and 3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_bundleValue

namespace StrategyproofMultidim

/-- **Quasilinear utility `u(μᵢ(w); x)`** (§3, p.5; used in Definitions 1 and 3, p.7).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.5: "u((d, p); vᵢ) := dᵢᵀvᵢ − pᵢ."

`util μ w i x = dᵢ(w)ᵀx − pᵢ(w)` is the utility of buyer `i`, whose true valuation vector is `x`,
from the outcome the mechanism `μ` selects at the reported profile `w`. -/
def util {n m : ℕ} (μ : Mechanism n m) (w : Fin n → Fin m → ℝ) (i : Fin n) (x : Fin m → ℝ) : ℝ :=
  bundleValue (μ.q w i) x - μ.t i w

end StrategyproofMultidim


