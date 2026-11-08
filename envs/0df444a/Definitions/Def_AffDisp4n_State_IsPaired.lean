-- Prove2me | Definitions.Def_AffDisp4n_State_IsPaired
-- name    : AffDisp4n_State_IsPaired
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:57.838199+00:00
-- url     : https://prove2.me/theorems/ef9c3e03-90cc-4cf1-996d-b21d6cbba166
-- title:
--   Paired parameter
-- statement:
--   A parameter $x$ is **paired** if it belongs to some pair of $P$, and **unpaired** otherwise.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.2, p.13

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- A parameter `x` is **paired** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.2, p.13) if it belongs to a pair of `P`; otherwise it is
unpaired. -/
def State.IsPaired {n : ℕ} (σ : State n) (x : Fin σ.m) : Prop := ∃ y : Fin σ.m, s(x, y) ∈ σ.P

end AffDisp4n


