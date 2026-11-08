-- Prove2me | Definitions.Def_AffDisp4n_State_AffineMovable
-- name    : AffDisp4n_State_AffineMovable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:58.9072+00:00
-- url     : https://prove2.me/theorems/e7d050c7-4776-469a-97ce-2673529fd644
-- title:
--   An affine gate can be moved into the affine system
-- statement:
--   **An affine gate can be moved** into the affine system if some gate $J$ of the acyclic part has an affine operation $b_1 t_1 + b_2 t_2 + c$ and each of its inputs $t_1, t_2$ is a constant, a parameter or an auxiliary variable. The move replaces $J$ by the equation $J + b_1 t_1 + b_2 t_2 = c$, and $J$ becomes an auxiliary variable.
--
--   When no gate can be moved, every affine gate of the acyclic part has an AND-type ancestor.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.3, p.15

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_IsAffineOp
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **An affine gate can be moved into the affine system** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.3 "Moving new gates into the affine
system", p.15): some gate of the acyclic part has an affine operation and both of its inputs are
constants, parameters or auxiliary variables (not gates).

**Formalization Note** When no gate can be moved, every affine gate has an AND-type ancestor, which is
the paper's condition at the end of the moves (p.15, p.22). -/
def State.AffineMovable {n : ℕ} (σ : State n) : Prop :=
  ∃ g : Fin σ.circ.size, IsAffineOp (σ.circ.op g) ∧ ¬ (σ.circ.in₁ g).IsGate ∧ ¬ (σ.circ.in₂ g).IsGate

end AffDisp4n


