-- Prove2me | Definitions.Def_AffDisp4n_State_eval
-- name    : AffDisp4n_State_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T08:00:15.941905+00:00
-- url     : https://prove2.me/theorems/c0ce7e74-e13c-40ed-9af3-a2ccb3c0351e
-- title:
--   Value $C(u)$ of a fair semi-circuit
-- statement:
--   When the auxiliary matrix $A$ is invertible, every parameter assignment $u$ extends uniquely to the auxiliary variables, $v = A^{-1} N u + A^{-1} c$. The value $C(u)$ of the fair semi-circuit is the value of its acyclic part on these parameter and auxiliary values. The companions `auxVal` and `inVal` give the solved auxiliary variables and all input values.
--
--   **Formalization Note** `A⁻¹` is Mathlib's matrix inverse. When $A$ is singular it is the zero matrix, but every statement of the mission requires $A$ invertible.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.3, pp.13–14

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- The **auxiliary variables as functions of the parameters** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.3, p.14):
`v = A⁻¹ N u + A⁻¹ c`, the unique solution of the affine system when `A` is invertible. -/
noncomputable def State.auxVal {n : ℕ} (σ : State n) (u : Fin σ.m → ZMod 2) : Fin σ.r → ZMod 2 :=
  σ.A⁻¹.mulVec (σ.N.mulVec u + σ.c)

/-- The values of all inputs of the acyclic part: parameters `u` and auxiliary variables
`A⁻¹(N u + c)`. -/
noncomputable def State.inVal {n : ℕ} (σ : State n) (u : Fin σ.m → ZMod 2) : Fin σ.m ⊕ Fin σ.r → ZMod 2 :=
  Sum.elim u (σ.auxVal u)

/-- The **value `C(u)` of the fair semi-circuit** of a state on the parameter assignment `u`
(Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.3, p.14: "every parameter assignment u extends uniquely to an assignment to all internal
values that satisfies every equation in the affine system and gives every gate of the acyclic part the
value of its operation on its inputs"). -/
noncomputable def State.eval {n : ℕ} (σ : State n) (u : Fin σ.m → ZMod 2) : ZMod 2 :=
  σ.circ.eval (σ.inVal u)

end AffDisp4n


