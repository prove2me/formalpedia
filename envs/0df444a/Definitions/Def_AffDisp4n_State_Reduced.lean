-- Prove2me | Definitions.Def_AffDisp4n_State_Reduced
-- name    : AffDisp4n_State_Reduced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T08:02:34.85279+00:00
-- url     : https://prove2.me/theorems/68017deb-ef6f-4d4a-aa29-b78bcd4e734e
-- title:
--   No deletion or move applies
-- statement:
--   A state is **reduced** if none of the deletions (D1)–(D4) applies and no affine gate can be moved into the affine system. This is the state reached in §4.1 after "we repeatedly apply the deletions (D1)—(D4) and move every gate with an affine operation and no AND-type ancestor into the affine system … until none of them is applicable".
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.22

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_D1Applicable
import Definitions.Def_AffDisp4n_State_D2Applicable
import Definitions.Def_AffDisp4n_State_D3Applicable
import Definitions.Def_AffDisp4n_State_D4Applicable
import Definitions.Def_AffDisp4n_State_AffineMovable

namespace AffDisp4n

/-- A state is **reduced** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1, p.22: "we repeatedly apply the deletions (D1)–(D4) and move every
gate with an affine operation and no AND-type ancestor into the affine system, until none of them is
applicable"): none of (D1)–(D4) applies and no affine gate can be moved into the affine system. -/
def State.Reduced {n : ℕ} (σ : State n) : Prop :=
  ¬ σ.D1Applicable ∧ ¬ σ.D2Applicable ∧ ¬ σ.D3Applicable ∧ ¬ σ.D4Applicable ∧ ¬ σ.AffineMovable

end AffDisp4n


