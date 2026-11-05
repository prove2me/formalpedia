-- Prove2me | Definitions.Def_RotationLadder_Protocol_ketZ
-- name    : RotationLadder_Protocol_ketZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:40.502801+00:00
-- url     : https://prove2.me/theorems/29f52896-022a-4671-aff7-3db0c316d78b
-- title:
--   Resource state $|Z(\alpha)\rangle=(|0\rangle+e^{i\alpha}|1\rangle)/\sqrt2$
-- statement:
--   For a real angle $\alpha$, the resource state of the rotation circuit is
--
--   $$|Z(\alpha)\rangle=\frac{1}{\sqrt2}\bigl(|0\rangle+e^{i\alpha}|1\rangle\bigr).$$
--
--   It lies in the $XY$-plane of the Bloch sphere. Consumed by the circuit of Fig. 1, it applies a rotation by $\pm\alpha$ about the $Z$-axis.
--
--   **Formalization Note** The vector is normalized; the paper suppresses the factor $1/\sqrt2$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2

import Mathlib

namespace RotationLadder.Protocol

/-- **The resource state `|Z(α)⟩`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, unnumbered, p. 2: "`|Z(θ)⟩ = |0⟩ + e^(iθ) |1⟩`".

**Formalization Note.** The vector is normalized, `(|0⟩ + e^(iα)|1⟩)/√2`; the paper suppresses the
factor `1/√2`. This factor is the source of the amplitudes `1/√2` in the statements about Fig. 1. -/
noncomputable def ketZ (α : ℝ) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun q =>
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if q then Complex.exp (Complex.I * (α : ℂ)) else 1)

end RotationLadder.Protocol


