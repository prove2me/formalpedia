-- Prove2me | Definitions.Def_RotationLadder_Protocol_residual
-- name    : RotationLadder_Protocol_residual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:40.142328+00:00
-- url     : https://prove2.me/theorems/bf827f3d-4d85-45f3-9f1a-0e1ed771e1bb
-- title:
--   Remaining angle $r_t$ of a run
-- statement:
--   Fix a target angle $\varphi$, a rule $\mathrm{pick}$ and outcomes $\omega$. The remaining angle starts at $r_0=\varphi$, and a remaining angle $0$ stays $0$. Otherwise, with $i=\mathrm{pick}(r_t)$,
--
--   $$r_{t+1}=\begin{cases}r_t-\operatorname{sign}(r_t)\,\pi/4&\text{if }i=0,\\ r_t-(-1)^{\omega_t}\,2\theta_i&\text{if }i\ge1.\end{cases}$$
--
--   For $i\ge1$, outcome $m$ applies the rotation $Z((-1)^m2\theta_i)$. Level 0 is deterministic because a failed $T$ gate is corrected by the phase gate $S$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, pp. 3-4

import Mathlib
import Definitions.Def_RotationLadder_Protocol_angle
import Definitions.Def_RotationLadder_Protocol_Coins

namespace RotationLadder.Protocol

/-- **The remaining angle of a run.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, pp. 3-4: apply the level closest to the target "and then recurse. The next gate to
apply will depend on whether the current gate succeeded or not."

`residual pick φ ω t` is the angle still to apply after `t` steps towards `Z(φ)`:
`r_0 = φ`; a zero residual stays zero; with `i = pick r_t`, a level `i ≥ 1` gives
`r_(t+1) = r_t - (-1)^(ω t) · 2θ_i`, since outcome `m` applies `Z((-1)^m 2θ_i)`; level `0` gives
`r_(t+1) = r_t - sign(r_t) · π/4` whatever the outcome.

**Formalization Note.** Level `0` is deterministic by p. 3: "if a `T` gate fails (using a `|H_0⟩`
state), we can always correct deterministically by applying the phase gate `S`". The paper's step
list on p. 4 does not repeat this. `runKet` carries the corresponding correction. -/
noncomputable def residual (pick : ℝ → ℕ) (φ : ℝ) (ω : Coins) : ℕ → ℝ
  | 0 => φ
  | t + 1 =>
    if residual pick φ ω t = 0 then 0
    else if pick (residual pick φ ω t) = 0 then
      residual pick φ ω t - Real.sign (residual pick φ ω t) * (Real.pi / 4)
    else
      residual pick φ ω t - (if ω t then (-1 : ℝ) else 1) * angle (pick (residual pick φ ω t))

end RotationLadder.Protocol


