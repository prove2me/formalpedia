-- Prove2me | Definitions.Def_StrategyproofMultidim_bundleValue
-- name    : StrategyproofMultidim_bundleValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:39.395711+00:00
-- url     : https://prove2.me/theorems/bcc35963-42b4-4f2c-8cfd-cd4020dc5beb
-- title:
--   Value of a bundle $d_i^{\top}v_i$
-- statement:
--   For a decision vector $b\in\{0,1\}^m$ and a valuation vector $x\in\mathbb R^m$, the **value of the bundle** is
--   $$b^{\top}x=\sum_{k\in M} b^k x^k,$$
--   the total value of the objects in the bundle. It is the first term of the quasilinear utility $u((d,p);v_i)=d_i^{\top}v_i-p_i$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.5 (PDF p.6)

import Mathlib

namespace StrategyproofMultidim

/-- **Value of a bundle, `dᵢᵀvᵢ`** (§3, p.5).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.5: "utility of each pair of decision matrix and price vector (d, p) is given by
u((d, p); vᵢ) := dᵢᵀvᵢ − pᵢ."

`bundleValue b x = ∑ₖ bₖ xₖ` is the inner product of a decision vector `b ∈ {0,1}ᵐ` with a
valuation vector `x`: the total value of the objects in the bundle `b`. -/
def bundleValue {m : ℕ} (b : Fin m → Bool) (x : Fin m → ℝ) : ℝ :=
  ∑ k, if b k then x k else 0

end StrategyproofMultidim


