-- Prove2me | Definitions.Def_AvoidPlast_queries
-- name    : AvoidPlast_queries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:45:29.899207+00:00
-- url     : https://prove2.me/theorems/63d0b3df-e2e9-4d68-ac16-cd14631a2000
-- title:
--   Positions read on a read-only tape
-- statement:
--   The set of positions of the string on a read-only tape that are read during a halting run: the head positions at the steps before halting, inside the string. For a verifier this is its set of queries, used for query complexity and non-adaptivity.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.1, p.17

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_run
import Definitions.Def_AvoidPlast_haltTime

namespace AvoidPlast

/-- The set of positions of the string on read-only tape `j` that are read during a halting run
(Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.1, p.17, "queries"): the head positions at the steps before halting, inside the
string. -/
noncomputable def queries {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) (j : Fin r) :
    Finset ℕ :=
  ((Finset.range (haltTime M xs)).image fun t => (run M xs t).inPos j).filter
    (fun p => p < (xs j).length)

end AvoidPlast


