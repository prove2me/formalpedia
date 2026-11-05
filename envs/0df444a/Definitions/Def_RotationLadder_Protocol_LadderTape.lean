-- Prove2me | Definitions.Def_RotationLadder_Protocol_LadderTape
-- name    : RotationLadder_Protocol_LadderTape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:00.775455+00:00
-- url     : https://prove2.me/theorems/fafaae9d-2b85-4205-844d-2e0b86e54dd0
-- title:
--   Randomness of one ladder run
-- statement:
--   A ladder run is driven by a sequence $u=(u_0,u_1,\dots)$ of points of $[0,1]$, one for each step of the walk of Fig. 3.
--
--   **Formalization Note** A step at level $L$ goes up when $u_t<p_{0,L}$, so a uniform $u_t$ gives the outcome probabilities of the circuit.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3 and Fig. 3

import Mathlib

namespace RotationLadder.Protocol

/-- **The randomness of one ladder.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, p. 3, Fig. 3: one uniform variable per step of the walk.

**Formalization Note.** Step `t` goes up when `u t < p_(0,i)`; see `ladderLevel`. -/
abbrev LadderTape : Type := ℕ → unitInterval

end RotationLadder.Protocol


