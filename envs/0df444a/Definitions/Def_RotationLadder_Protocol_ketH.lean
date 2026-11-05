-- Prove2me | Definitions.Def_RotationLadder_Protocol_ketH
-- name    : RotationLadder_Protocol_ketH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:40.098125+00:00
-- url     : https://prove2.me/theorems/60f66bd1-3d53-4204-99ec-2f8fbfe865b1
-- title:
--   Ladder state $|H_i\rangle=\cos\theta_i|0\rangle+\sin\theta_i|1\rangle$
-- statement:
--   The ladder state at level $i$ is the unit vector
--
--   $$|H_i\rangle=\cos\theta_i\,|0\rangle+\sin\theta_i\,|1\rangle .$$
--
--   Level 0 is the magic state $|H\rangle=\cos(\pi/8)|0\rangle+\sin(\pi/8)|1\rangle$, an eigenstate of the Hadamard operation, which the protocol takes as its only non-Clifford input.
--
--   **Formalization Note** The computational basis is indexed by booleans, with `false` for $|0\rangle$ and `true` for $|1\rangle$.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 2

import Mathlib
import Definitions.Def_RotationLadder_Protocol_theta

namespace RotationLadder.Protocol

/-- **The ladder state `|H_i⟩`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, p. 2: "`|H_i⟩ = cos θ_i |0⟩ + sin θ_i |1⟩`".

**Formalization Note.** A qubit's basis index is a `Bool`, `false` = `|0⟩`, `true` = `|1⟩`.
`ketH 0` is the paper's `|H⟩ = |H_0⟩`. -/
noncomputable def ketH (i : ℤ) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun q => if q then (Real.sin (theta i) : ℂ) else (Real.cos (theta i) : ℂ)

end RotationLadder.Protocol


