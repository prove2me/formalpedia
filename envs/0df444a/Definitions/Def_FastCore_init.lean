-- Prove2me | Definitions.Def_FastCore_init
-- name    : FastCore_init
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:29.97799+00:00
-- url     : https://prove2.me/theorems/8e69dc45-1333-447f-9404-103d7465806f
-- title:
--   Initial configuration of Algorithm 1
-- statement:
--   A run starts in the outer loop with $\pi^{(0)}=\bar\pi^{(0)}=0$, $t=0$, $S_0=N$, an empty record of the sets $T_t$, and zero oracle calls and zero additional time.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1, lines 1–2, p.15

import Mathlib
import Definitions.Def_FastCore_Phase
import Definitions.Def_FastCore_Cfg

namespace FastCore

/-- The initial configuration (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1, lines 1–2, p.15): `π^(0) = π̄^(0) = 0`, `t = 0`,
`S₀ = N`. The fields `wN`, `Δl`, `Δh` are set before they are read. -/
noncomputable def init (n : ℕ) : Cfg n where
  phase := Phase.outer
  t := 0
  S := Finset.univ
  π := 0
  πbar := 0
  wN := 0
  Δl := 0
  Δh := 1
  log := []
  calls := 0
  ticks := 0

end FastCore


