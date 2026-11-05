-- Prove2me | Definitions.Def_RotationLadder_Protocol_zRot
-- name    : RotationLadder_Protocol_zRot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:46.679238+00:00
-- url     : https://prove2.me/theorems/3a6ae92b-2dc1-422d-af3a-c471ec4fb071
-- title:
--   $Z$-rotation $Z(\alpha)=\mathrm{diag}(1,e^{i\alpha})$
-- statement:
--   The rotation by $\alpha$ about the $Z$-axis is the diagonal unitary
--
--   $$Z(\alpha)=\begin{pmatrix}1&0\\0&e^{i\alpha}\end{pmatrix},$$
--
--   sending $a|0\rangle+b|1\rangle$ to $a|0\rangle+be^{i\alpha}|1\rangle$. In particular $Z(\pi/4)$ is the $T$ gate and $Z(\pi/2)$ the phase gate $S$.
--
--   **Formalization Note** This is the paper's own phase convention, not the half-angle form $\mathrm{diag}(e^{-i\alpha/2},e^{i\alpha/2})$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2

import Mathlib

namespace RotationLadder.Protocol

/-- **The `Z`-rotation `Z(α)`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, unnumbered, p. 2: the rotation sends `a|0⟩ + b|1⟩` to `a|0⟩ + b e^(iθ)|1⟩`.

`zRot α = diag(1, e^(iα))`.

**Formalization Note.** The paper's own phase convention, not the half-angle form
`diag(e^(-iα/2), e^(iα/2))`: `zRot (π/4)` is the `T` gate and `zRot (π/2)` the phase gate `S`. -/
noncomputable def zRot (α : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp (Complex.I * (α : ℂ)) else 1

end RotationLadder.Protocol


