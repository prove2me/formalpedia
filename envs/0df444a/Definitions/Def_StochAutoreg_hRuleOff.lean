-- Prove2me | Definitions.Def_StochAutoreg_hRuleOff
-- name    : StochAutoreg_hRuleOff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:37.725247+00:00
-- url     : https://prove2.me/theorems/27b99e91-d78a-48b8-9011-65d30fd74291
-- title:
--   Inactive rule $h_0$ of the family $H_D$
-- statement:
--   The inactive generator $h_0$ of $H_D$ sets, at each root $x_j$, $0\le j\le D$: $p_{h_0}(x_j)=0$ and $p_{h_0}(x_jz)=\tfrac12$ for $0<|z|<M$. Every root then has final mean $1/2$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, "The second family H_D", p.15

import Mathlib
import Definitions.Def_StochAutoreg_clampI

namespace StochAutoreg

/-- The inactive generator `h₀` of the family `H_D`: `p_{h₀}(x_j) = 0` and `p_{h₀}(x_j z) = 1/2` for `0 < |z| < M`, at each
of the roots `x₀, …, x_D`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "The second family `H_D`", p.15. -/
noncomputable def hRuleOff (D : ℕ) : Fin (D + 1) → List Bool → unitInterval :=
  fun _ z => clampI (if z = [] then 0 else 1 / 2)

end StochAutoreg


