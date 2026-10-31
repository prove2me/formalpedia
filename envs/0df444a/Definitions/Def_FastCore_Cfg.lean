-- Prove2me | Definitions.Def_FastCore_Cfg
-- name    : FastCore_Cfg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:30.182342+00:00
-- url     : https://prove2.me/theorems/71cdc206-6f65-40fa-b9b2-69f265bdd0c1
-- title:
--   Configuration of Algorithm 1
-- statement:
--   A **configuration** records the state of Algorithm 1 and Core-Search: the control location, the counter $t$, the active set ($S_t$ in the outer loop, $S_{t+1}$ during the search), the core point $\pi^{(t)}$, the point $\bar\pi^{(t)}$, the value $w(N)$, the bisection endpoints $\Delta_l,\Delta_h$, the sets $T_0,T_1,\dots$ found so far, the number of oracle calls, and the additional time.
--
--   **Formalization Note** The record of $T_0,T_1,\dots$ is ghost state: the transition function writes it and never reads it. It is the collection $\mathcal G_t$ of Proposition 1.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1 and Procedure 2, pp.15–16

import Mathlib
import Definitions.Def_FastCore_Phase

namespace FastCore

/-- A configuration of Algorithm 1 and Procedure 2 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, pp.15–16).

**Formalization Note.** `S` is `S_t` in phase `outer` and `S_(t+1)` in phase `search`; `π` is the
core point `π^(t)`, `πbar` is `π̄^(t)`, and `wN` holds `w(N)`, read off the first oracle answer. `log`
records `T₀, T₁, …` (the collections `G_t` of Proposition 1); it is ghost state, never read by
`step`. `calls` counts oracle calls. `ticks` is the additional time, in unit-cost operations. -/
structure Cfg (n : ℕ) where
  /-- The control location. -/
  phase : Phase
  /-- The counter `t` of Algorithm 1. -/
  t : ℕ
  /-- The active set. -/
  S : Finset (Fin n)
  /-- The current core point `π^(t)`. -/
  π : Fin n → ℝ
  /-- The point `π̄^(t)`. -/
  πbar : Fin n → ℝ
  /-- The value `w(N)`. -/
  wN : ℝ
  /-- The lower end of the bisection interval. -/
  Δl : ℝ
  /-- The upper end of the bisection interval. -/
  Δh : ℝ
  /-- The sets `T₀, T₁, …` found so far (ghost). -/
  log : List (Finset (Fin n))
  /-- The number of oracle calls so far. -/
  calls : ℕ
  /-- The additional time so far. -/
  ticks : ℕ

end FastCore


