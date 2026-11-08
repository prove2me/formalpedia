-- Prove2me | Definitions.Def_AffDisp4n_State_OutputSimple
-- name    : AffDisp4n_State_OutputSimple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:59.595063+00:00
-- url     : https://prove2.me/theorems/f7ffcf14-e3ad-4787-8648-7f509e3dc068
-- title:
--   The output check of §4.1 succeeds
-- statement:
--   **The output check succeeds** if the output of the current circuit has one of two forms: (i) a constant or a literal of a parameter or an auxiliary variable, or (ii) a literal of an AND-type gate whose two parents are constants, parameters or auxiliary variables. Then the output is of the form required by Lemma 2.2, and gate elimination stops.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4.1, p.22

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_IsAndOp
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **The output check succeeds** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4.1, p.22): the output of the current circuit is (i) a constant
or a literal of a parameter or an auxiliary variable, or (ii) a literal of an AND-type gate whose two
parents are constants, parameters or auxiliary variables. -/
def State.OutputSimple {n : ℕ} (σ : State n) : Prop :=
  ¬ σ.circ.out.IsGate ∨
    ∃ g : Fin σ.circ.size, σ.circ.out = .gate g ∧ IsAndOp (σ.circ.op g) ∧
      ¬ (σ.circ.in₁ g).IsGate ∧ ¬ (σ.circ.in₂ g).IsGate

end AffDisp4n


