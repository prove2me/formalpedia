-- Prove2me | Definitions.Def_RotationLadder_Protocol_xRot
-- name    : RotationLadder_Protocol_xRot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:35.890097+00:00
-- url     : https://prove2.me/theorems/a0331eef-1092-4c58-94b8-0fac9b686f82
-- title:
--   $X$-rotation $X(\alpha)=HZ(\alpha)H$
-- statement:
--   The rotation by $\alpha$ about the $X$-axis is
--
--   $$X(\alpha)=H\,Z(\alpha)\,H,$$
--
--   where $H$ is the Hadamard gate, which exchanges the $X$- and $Z$-axes of the Bloch sphere.
--
--   **Formalization Note** The paper does not write $X(\alpha)$ as a matrix. It says that an analogous circuit performs a rotation about the $X$-axis; this is that rotation, in the convention of $Z(\alpha)$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2 and Sec. III, unnumbered, p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_RotationLadder_Protocol_zRot

namespace RotationLadder.Protocol

/-- **The `X`-rotation `X(α)`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, unnumbered, p. 2: "An analogous circuit performs a rotation about the `X`-axis";
Sec. III, p. 5: `U ∝ X(α)Z(β)X(γ)`.

`xRot α = H Z(α) H`.

**Formalization Note.** The paper does not write `X(α)` as a matrix; this is the `Z`-rotation
conjugated by the Clifford `H`, which exchanges the `X`- and `Z`-axes. -/
noncomputable def xRot (α : ℝ) : Matrix Bool Bool ℂ :=
  QAlgorithms.hadamard * zRot α * QAlgorithms.hadamard

end RotationLadder.Protocol


