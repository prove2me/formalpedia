-- Prove2me | Definitions.Def_SigRoute_Arm
-- name    : SigRoute_Arm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:44.170696+00:00
-- url     : https://prove2.me/theorems/480d8cb4-dada-4912-8aba-1710f51b136c
-- title:
--   The two arms $A$ and $B$
-- statement:
--   A routed verification protocol has two **arm protocols** $\Pi_A$ and $\Pi_B$. In every round the verifier sends the round to one arm, its **route** $\rho_j\in\{A,B\}$.
--
--   This two-element type is the codomain of the routes and of the credit function $u:\{A,B\}\to\mathbb R$ used by every statement of the mission.
--
--   **Formalization Note** The type carries the discrete σ-algebra, so a route $\rho_j:\Omega\to\{A,B\}$ is measurable exactly when the events $\{\rho_j=A\}$ and $\{\rho_j=B\}$ are.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 5, step (R2), p.5

import Mathlib

namespace SigRoute

/-- The two arms `A` and `B` of a routed verification protocol: a round is sent to arm `ρ_j ∈ {A, B}`
(Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 5, step (R2), p.5).

**Formalization Note** `Arm` carries the discrete σ-algebra (every set is measurable), so a route
`ρ_j : Ω → Arm` is measurable exactly when each event `{ρ_j = X}` is. -/
inductive Arm
  | A
  | B
  deriving DecidableEq, Inhabited

instance : Fintype Arm :=
  ⟨{Arm.A, Arm.B}, fun x => by cases x <;> simp⟩

instance : MeasurableSpace Arm := ⊤

instance : DiscreteMeasurableSpace Arm := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end SigRoute


