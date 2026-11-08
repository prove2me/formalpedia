-- Prove2me | Definitions.Def_AffDisp4n_State_q
-- name    : AffDisp4n_State_q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:32.841629+00:00
-- url     : https://prove2.me/theorems/cc3ce081-e3ad-4613-8471-d1d827755bf7
-- title:
--   Number $q = |P|$ of pairs
-- statement:
--   The number $q = |P|$ of pairs of a state.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.4, p.16

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- The **number `q = |P|` of pairs** of a state (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.4, p.16). -/
def State.q {n : ℕ} (σ : State n) : ℕ := σ.P.card

end AffDisp4n


