-- Prove2me | Definitions.Def_AffDisp4n_State_s
-- name    : AffDisp4n_State_s
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:41.451092+00:00
-- url     : https://prove2.me/theorems/390a1589-4198-420a-9d23-5c881b287ca5
-- title:
--   Size $s$ of a fair semi-circuit
-- statement:
--   The **size** $s$ of the current fair semi-circuit is the number $r$ of equations plus the number of gates in the acyclic part. Initially $s = |C_0|$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.3, p.14

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- The **size `s`** of the current fair semi-circuit (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.3, p.14): the number `r` of equations
plus the number of gates in the acyclic part. -/
def State.s {n : ℕ} (σ : State n) : ℕ := σ.r + σ.circ.size

end AffDisp4n


