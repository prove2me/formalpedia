-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_HasDensity
-- name    : SelfCorrect3D_Memory_HasDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:46.011336+00:00
-- url     : https://prove2.me/theorems/9923519b-748f-4d58-91c4-265681c6d9b0
-- title:
--   Bounded density: at most $D$ qubits per unit ball
-- statement:
--   Qubit positions $\mathrm{pos}:\{1,\dots,n\}\to\mathbb R^3$ have **density at most $D$** if every closed ball of radius $1$ in $\mathbb R^3$ contains at most $D$ qubit positions (counted with multiplicity). This is condition 2 of Theorem 1.2: "Every unit ball in $\mathbb R^3$ contains $O(1)$ qubits."
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Theorem 1.2 (2), p. 4

import Mathlib

namespace SelfCorrect3D.Memory

open Classical in
/-- **Bounded density `D`.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, Theorem 1.2 (2), p. 4: "(Bounded
density) Every unit ball in ℝ³ contains O(1) qubits": every closed ball of radius `1` contains at
most `D` qubit positions.

**Formalization Note.** Qubits are counted with multiplicity (two qubits at one point count
twice); closed unit balls. -/
noncomputable def HasDensity {n : ℕ} (pos : Fin n → EuclideanSpace ℝ (Fin 3)) (D : ℕ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin 3),
    (Finset.univ.filter fun q => pos q ∈ Metric.closedBall x 1).card ≤ D

end SelfCorrect3D.Memory


