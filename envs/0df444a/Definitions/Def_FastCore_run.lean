-- Prove2me | Definitions.Def_FastCore_run
-- name    : FastCore_run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:06.617012+00:00
-- url     : https://prove2.me/theorems/526c1f10-374b-4f23-859b-b812c0c9f506
-- title:
--   The run of Algorithm 1
-- statement:
--   The configuration reached after $K$ transitions from the initial configuration, for a given oracle and precision. A halted run is at the return location, and its output is its current core point.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1 and Procedure 2, pp.15–16

import Mathlib
import Definitions.Def_FastCore_Cfg
import Definitions.Def_FastCore_Oracle
import Definitions.Def_FastCore_init
import Definitions.Def_FastCore_step

namespace FastCore

/-- The configuration after `K` transitions of Algorithm 1 from the initial configuration
(Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, pp.15–16). A halted run has `phase = done`, and its output is its field `π`. -/
noncomputable def run {n : ℕ} (q : Oracle n) (ε : ℝ) (K : ℕ) : Cfg n :=
  (step q ε)^[K] (init n)

end FastCore


