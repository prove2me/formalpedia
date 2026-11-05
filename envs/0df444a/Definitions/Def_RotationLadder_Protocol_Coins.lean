-- Prove2me | Definitions.Def_RotationLadder_Protocol_Coins
-- name    : RotationLadder_Protocol_Coins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:55.124455+00:00
-- url     : https://prove2.me/theorems/c2a6e262-e3d2-4649-83db-15f4d40337d8
-- title:
--   Measured outcomes of a run
-- statement:
--   A run of the rotation protocol is described by its sequence of outcomes $\omega=(\omega_0,\omega_1,\dots)$, where $\omega_t\in\{0,1\}$ is the outcome of Fig. 1 at step $t$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2 and Sec. III, unnumbered, p. 4

import Mathlib

namespace RotationLadder.Protocol

/-- **The measured outcomes of a run.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, p. 2: the outcome `m` of Fig. 1 at each step of the protocol.

`ω t` is the outcome of step `t`, `false` = `0`, `true` = `1`. -/
abbrev Coins : Type := ℕ → Bool

end RotationLadder.Protocol


