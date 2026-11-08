-- Prove2me | Definitions.Def_AvoidPlast_workSpace
-- name    : AvoidPlast_workSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:45:13.797212+00:00
-- url     : https://prove2.me/theorems/3a0d0aae-446a-4b09-a3d4-e8118cf4dfc9
-- title:
--   Work space
-- statement:
--   The work space of a halting run: the number of distinct cells (work tape, position) scanned during the run, the start cells included. Index tapes are work tapes and count; read-only tapes and the output tape do not. This is what makes "space $n^\gamma$" with $\gamma<1$ possible and meaningful, as the paper notes that the randomness tape does "not count towards the machine's space complexity" (p.3).
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13; Section 1.2, p.3

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_run
import Definitions.Def_AvoidPlast_haltTime

namespace AvoidPlast

/-- The work space of a halting run (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model, and p.3: the contents of
the randomness tape do "not count towards the machine's space complexity"): the number of distinct
cells (work tape, position) scanned during the run, the start cells included.

**Formalization Note** The index tapes are work tapes and count. The read-only tapes and the output
tape never count. -/
noncomputable def workSpace {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) : ℕ :=
  ((Finset.range (haltTime M xs + 1)).biUnion fun t =>
    Finset.univ.image fun j => (j, (run M xs t).workPos j)).card

end AvoidPlast


