-- Prove2me | Definitions.Def_AffDisp4n_State_Case1Applicable
-- name    : AffDisp4n_State_Case1Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T08:00:15.457714+00:00
-- url     : https://prove2.me/theorems/a0df258d-012f-4772-bcf1-6f6980d8d5fd
-- title:
--   Case 1 applies
-- statement:
--   **Case 1 applies** if some paired parameter has degree $0$ or degree at least $2$. When Case 1 does not apply, every paired parameter is isolated.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.22

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_IsPaired
import Definitions.Def_AffDisp4n_State_deg

namespace AffDisp4n

/-- **Case 1 applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1 "Case 1: a paired parameter has degree zero or at least two",
p.22). -/
def State.Case1Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ p : Fin σ.m, σ.IsPaired p ∧ (σ.deg p = 0 ∨ 2 ≤ σ.deg p)

end AffDisp4n


