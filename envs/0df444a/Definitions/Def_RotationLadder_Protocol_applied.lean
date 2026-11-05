-- Prove2me | Definitions.Def_RotationLadder_Protocol_applied
-- name    : RotationLadder_Protocol_applied
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:45.028861+00:00
-- url     : https://prove2.me/theorems/d90a7b58-299b-4520-8d02-ff4a0cce113f
-- title:
--   Angle applied by a stopped run
-- statement:
--   The rotation angle a run has applied when it stops is $\varphi-r_\tau$, for the stopping time $\tau$ of the run.
--
--   **Formalization Note** On the event $\tau=\infty$ the value is $0$. Every statement restricts to $\tau<\infty$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 4, step 6

import Mathlib
import Definitions.Def_RotationLadder_Protocol_stopTime

namespace RotationLadder.Protocol

/-- **The angle a run has applied when it stops.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, p. 4, step 6.

`applied pick φ ε ω = φ - r_τ` for the stopping time `τ = stopTime pick φ ε ω`.

**Formalization Note.** On `τ = ⊤` the value is `φ - r_0 = 0` by `ENat.toNat ⊤ = 0`; every statement
restricts to `τ < ⊤`. -/
noncomputable def applied (pick : ℝ → ℕ) (φ ε : ℝ) (ω : Coins) : ℝ :=
  φ - residual pick φ ω (stopTime pick φ ε ω).toNat

end RotationLadder.Protocol


