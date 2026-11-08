-- Prove2me | Definitions.Def_AffDisp4n_State_D2Applicable
-- name    : AffDisp4n_State_D2Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:13.241201+00:00
-- url     : https://prove2.me/theorems/6f579d5d-32c0-4f1f-8d1f-db9f5e43b703
-- title:
--   Deletion (D2) applies
-- statement:
--   **Deletion (D2) applies** to a state if some gate of the acyclic part has no children and is not the designated output.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, p.20

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **(D2) applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1 "D2: deleting an unused gate", p.20): some gate has no children (no
gate reads it) and is not the designated output. -/
def State.D2Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ g : Fin σ.circ.size, (∀ h : Fin σ.circ.size, ¬ σ.circ.ReadsGate h g) ∧ σ.circ.out ≠ .gate g

end AffDisp4n


