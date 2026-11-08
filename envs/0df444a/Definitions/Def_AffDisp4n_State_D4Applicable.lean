-- Prove2me | Definitions.Def_AffDisp4n_State_D4Applicable
-- name    : AffDisp4n_State_D4Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:57.88201+00:00
-- url     : https://prove2.me/theorems/218cca64-cffe-428d-9a1b-1c6cacb8e5bf
-- title:
--   Deletion (D4) applies
-- statement:
--   **Deletion (D4) applies** to a state if there is an unpaired, isolated parameter $x$ whose unique child is an equation: $x$ has degree $1$ and appears in some equation.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, p.20

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_IsPaired
import Definitions.Def_AffDisp4n_State_deg

namespace AffDisp4n

/-- **(D4) applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1 "D4: unit parameter deletion", p.20): there is an unpaired, isolated
(degree one) parameter `x` whose unique child is an equation. -/
def State.D4Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ x : Fin σ.m, ¬ σ.IsPaired x ∧ σ.deg x = 1 ∧ ∃ i : Fin σ.r, σ.N i x ≠ 0

end AffDisp4n


