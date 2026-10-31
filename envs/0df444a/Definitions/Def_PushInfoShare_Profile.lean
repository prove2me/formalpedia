-- Prove2me | Definitions.Def_PushInfoShare_Profile
-- name    : PushInfoShare_Profile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:59.75084+00:00
-- url     : https://prove2.me/theorems/b2b0c5da-8d97-4b9e-bfdb-39425312058d
-- title:
--   Strategy profile of the pricing and ordering stage
-- statement:
--   A strategy profile consists of
--
--   1. the coefficients $\alpha_i,B_i$ of each manufacturer's linear price rule $w_i=\alpha_i+B_iY_i$;
--   2. the retailer's order rule $q_i(w,y)$, giving the order of product $i$ at wholesale prices $w=(w_1,w_2)$ and signals $y=(y_1,y_2)$.
--
--   The price rules are the linear strategies to which the paper restricts attention.
--
--   **Formalization Note** The order rule receives both signals. In an equilibrium it cannot use a signal that was not shared, since it must solve the retailer's problem at a forecast that ignores that signal. The sign of $B_i$ is left free.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.9

import Mathlib

namespace PushInfoShare

/-- A strategy profile of the wholesale-pricing and ordering stage, Jain, SSRN:3388957 (PDF of
2021-04-25), §3, p.9: manufacturer `i` prices linearly in its signal, `wᵢ = α i + B i * Yᵢ`, and
`q i w y` is the retailer's order of product `i` when the wholesale prices are `w` and the signals
are `y`.

**Formalization Note.** `q` receives every signal, including one not shared. It cannot use an
unshared signal in an equilibrium, because `IsLinearSeparatingEq` requires `q i w y` to solve the
retailer's problem at a forecast that ignores it. The sign of `B` is left free. -/
structure Profile where
  α : Fin 2 → ℝ
  B : Fin 2 → ℝ
  q : Fin 2 → (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ

end PushInfoShare


