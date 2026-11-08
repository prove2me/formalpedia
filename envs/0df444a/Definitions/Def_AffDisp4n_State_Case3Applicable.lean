-- Prove2me | Definitions.Def_AffDisp4n_State_Case3Applicable
-- name    : AffDisp4n_State_Case3Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:52.620736+00:00
-- url     : https://prove2.me/theorems/27d86445-4ade-4a2e-a112-206109ffa251
-- title:
--   Case 3 applies
-- statement:
--   **Case 3 applies** if some paired parameter occurs in the affine system, i.e. appears with a nonzero coefficient in some equation.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.23

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_IsPaired

namespace AffDisp4n

/-- **Case 3 applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1 "Case 3: a paired parameter occurs in the affine system", p.23). -/
def State.Case3Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ p : Fin σ.m, σ.IsPaired p ∧ ∃ i : Fin σ.r, σ.N i p ≠ 0

end AffDisp4n


