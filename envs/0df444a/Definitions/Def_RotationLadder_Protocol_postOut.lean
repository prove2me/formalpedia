-- Prove2me | Definitions.Def_RotationLadder_Protocol_postOut
-- name    : RotationLadder_Protocol_postOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:59.079309+00:00
-- url     : https://prove2.me/theorems/05917528-cc42-4c08-8f50-2b98b4065a2b
-- title:
--   Post-measurement vector of the second wire
-- statement:
--   Let $v$ be a two-qubit vector and $m\in\{0,1\}$. The unnormalized state of the second wire when the first wire is measured with outcome $m$ is
--
--   $$(\langle m|\otimes 1)\,v .$$
--
--   Its squared norm is the probability of the outcome $m$, so the statements about Figs. 1 and 2 carry the amplitudes explicitly.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2

import Mathlib

namespace RotationLadder.Protocol

/-- **Measuring the first wire.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, p. 2: "Upon measurement of the first qubit in the computational basis".

`postOut m v` is the unnormalized state of the second wire when the first wire of `v` reads `m`:
`(⟨m| ⊗ 1) v`. Its squared norm is the probability of the outcome `m`.

**Formalization Note.** `false` is the outcome `0` and `true` the outcome `1`. -/
noncomputable def postOut (m : Bool) (v : EuclideanSpace ℂ (Bool × Bool)) :
    EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun q => v (m, q)

end RotationLadder.Protocol


