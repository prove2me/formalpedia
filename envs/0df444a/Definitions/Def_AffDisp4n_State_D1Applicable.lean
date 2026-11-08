-- Prove2me | Definitions.Def_AffDisp4n_State_D1Applicable
-- name    : AffDisp4n_State_D1Applicable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T08:01:26.521125+00:00
-- url     : https://prove2.me/theorems/158c9fe0-28e2-4129-99d4-92fec17f3b3b
-- title:
--   Deletion (D1) applies
-- statement:
--   **Deletion (D1) applies** to a state if some gate $J$ of the acyclic part depends on at most one of its inputs, in one of two ways:
--
--   1. $J$ is constant on all parameter assignments in $Z(P)$;
--   2. $J$ computes $t + c$ for every parameter assignment, where $t$ is its first or its second input and $c \in \mathbb F_2$.
--
--   The second way covers constant and unary gates, gates with a constant input, gates with identical inputs, and AND-type gates whose inputs have dependent linear parts.
--
--   **Formalization Note** Gate values are functions of the parameters, with the auxiliary variables solved from the affine system.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, p.19

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_eval

namespace AffDisp4n

/-- **(D1) applies** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1 "D1: deleting a gate that depends on at most one input", p.19): some
gate `J` of the acyclic part computes a constant or a literal of one of its inputs. Concretely, either
1. `J` is constant on all parameter assignments in `Z(P)` ("if a gate becomes constant on all parameter
   assignments in Z(P) at some step, we also delete this gate by (D1)"), or
2. `J` computes `t + c` for every parameter assignment, where `t` is its first or its second input and
   `c ∈ 𝔽₂` (constant and unary gates, gates with identical inputs, AND-type gates whose inputs have
   dependent linear parts).

**Formalization Note** Gate values are taken as functions of the parameters `u`, with the auxiliary
variables solved as `A⁻¹(N u + c)`. -/
def State.D1Applicable {n : ℕ} (σ : State n) : Prop :=
  ∃ g : Fin σ.circ.size,
    (∃ c : ZMod 2, ∀ u ∈ Z σ.P, σ.circ.gateVal (σ.inVal u) g = c) ∨
    (∃ c : ZMod 2, ∀ u, σ.circ.gateVal (σ.inVal u) g =
        (σ.circ.in₁ g).val (σ.inVal u) (σ.circ.prevVal (σ.inVal u) g) + c) ∨
    (∃ c : ZMod 2, ∀ u, σ.circ.gateVal (σ.inVal u) g =
        (σ.circ.in₂ g).val (σ.inVal u) (σ.circ.prevVal (σ.inVal u) g) + c)

end AffDisp4n


