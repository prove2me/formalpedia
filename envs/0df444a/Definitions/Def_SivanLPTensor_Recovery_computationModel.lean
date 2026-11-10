-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_computationModel
-- name    : SivanLPTensor_Recovery_computationModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:34:08.651193+00:00
-- url     : https://prove2.me/theorems/719ed738-829d-499a-af73-da53968cc2df
-- title:
--   Input and execution interface for the determinant contraction routine
-- statement:
--   The contraction routine reads the dense tensor followed by the row-major entries of a covector frame $P$. Its output is the full skew matrix from formula (5), in the original block-coordinate order. The required execution property is
--   $$\text{arithmetic count}\le C\,N m^5,$$
--   where one positive constant $C$ works before all mode sizes, tensors and frames. No root instructions are used. The count is the machine's executed scalar-operation count; $C$ is existential because the source provides an asymptotic estimate, not a numerical constant. This property is not asserted here: the computational-form theorem must produce a finite program satisfying it.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Corollary 3.2 and (5), printed p. 6 / PDF p. 8; complexity proof, printed p. 9 / PDF p. 11

import Definitions.Def_SivanLPTensor_Recovery_algorithmModel

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators

/-- Input for the determinant implementation of (5): T, then the row-major P array. -/
def contractionInput {d : ℕ} {n : Fin (d + 2) → ℕ} (T : Tensor n)
    (P : Matrix (Fin d) (BlockIndex n) ℝ) : MachineInput :=
  let x := encodeInput T
  let D := ∑ j, n j
  { x with entries := fun t => if t < inputSize n then x.entries t else
      let s := t - inputSize n
      if h : s / D < d then
        ∑ z : BlockIndex n, if offset z = s % D then P ⟨s/D,h⟩ z else 0
      else 0 }

/-- Actual executions, no roots, and the O(N m⁵) bound from printed page 9.
C is an absolute existential constant, rather than an invented source constant. -/
def ComputesContractions (p : Program) (C : ℕ) : Prop :=
  0 < C ∧ ∀ (d : ℕ) (n : Fin (d + 2) → ℕ), 1 ≤ d → (∀ j, 0 < n j) →
    ∀ (T : Tensor n) (P : Matrix (Fin d) (BlockIndex n) ℝ) seed,
      ∃ t,
        let s := machineRun p (contractionInput T P) seed t
        s.stopped = true ∧ s.rootDegrees = [] ∧
        s.arithmetic ≤ C * inputSize n * (d + 2) ^ 5 ∧
        ∀ x y, s.real (offset x * (∑ j, n j) + offset y) = omegaFormula T P x y

end SivanLPTensor.Recovery


