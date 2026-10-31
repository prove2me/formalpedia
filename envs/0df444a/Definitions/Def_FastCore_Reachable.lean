-- Prove2me | Definitions.Def_FastCore_Reachable
-- name    : FastCore_Reachable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:28.155461+00:00
-- url     : https://prove2.me/theorems/7439d781-6979-4802-9fe9-a3fdcf3878b6
-- title:
--   Configurations of a run
-- statement:
--   A configuration is **reachable** if it occurs in the run of Algorithm 1 for the given oracle and precision. The invariants of Proposition 1 are statements about reachable configurations.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1 and Procedure 2, pp.15–16

import Mathlib
import Definitions.Def_FastCore_Cfg
import Definitions.Def_FastCore_Oracle
import Definitions.Def_FastCore_run

namespace FastCore

/-- `c` occurs in the run of Algorithm 1 with oracle `q` and precision `ε`
(Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, pp.15–16). -/
def Reachable {n : ℕ} (q : Oracle n) (ε : ℝ) (c : Cfg n) : Prop :=
  ∃ K, c = run q ε K

end FastCore


