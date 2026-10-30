-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P42
-- name    : QAlgorithms_Papers_Independent_Advance50_P42
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:05:31.423207+00:00
-- url     : https://prove2.me/theorems/f726120a-69f3-4da9-9fcb-2b73582d88b6
-- title:
--   Definitions for Asymptotic security of discrete-modulation protocols for continuous-variable quantum key distribution
-- statement:
--   The objects the formalized statements of *Asymptotic security of discrete-modulation protocols for continuous-variable quantum key distribution* (arXiv:1901.10099) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `phaseRotation`: Opposite phase rotations on the two real quadrature pairs, (153), PDF p.21. Coordinates 0,1,2,3 correspond to the paper's 1,2,3,4.
--   - `fourPhaseAverage`: The literal four-element matrix average (154), PDF p.21. This definition makes no claim that centered covariance is affine under state mixing.
--   - `phaseSymmetricMatrix`: The entire symmetric matrix in (156), PDF p.21; c1 is the sine entry. No quantum uncertainty premise is attached to arbitrary real parameters.
-- source:
--   Asymptotic security of discrete-modulation protocols for continuous-variable quantum key distribution, arXiv:1901.10099v4, https://arxiv.org/abs/1901.10099v4

import Mathlib

/-!
Kaur, Guha and Wilde, arXiv:1901.10099v4.
Only the independently algebraic Appendix B node is stated here.
The remaining full-paper nodes are explicitly accounted for in HARD.md and GAPS.json.
No finite cutoff or finite-dimensional surrogate for a bosonic theorem is asserted.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Advance50.P42

/-- Opposite phase rotations on the two real quadrature pairs, (153), PDF p.21.
Coordinates 0,1,2,3 correspond to the paper's 1,2,3,4. -/
def phaseRotation (phi : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cos phi, Real.sin phi, 0, 0;
     -Real.sin phi, Real.cos phi, 0, 0;
     0, 0, Real.cos phi, -Real.sin phi;
     0, 0, Real.sin phi, Real.cos phi]

/-- The literal four-element matrix average (154), PDF p.21.
This definition makes no claim that centered covariance is affine under state mixing. -/
def fourPhaseAverage (sigma : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 4 : ℝ) • ∑ k : Fin 4,
    phaseRotation (Real.pi * (k.val : ℝ) / 2) * sigma *
      (phaseRotation (Real.pi * (k.val : ℝ) / 2)).transpose

/-- The entire symmetric matrix in (156), PDF p.21; c1 is the sine entry.
No quantum uncertainty premise is attached to arbitrary real parameters. -/
def phaseSymmetricMatrix (a b c1 c2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a, 0, c2, c1;
     0, a, c1, -c2;
     c2, c1, b, 0;
     c1, -c2, 0, b]

example : phaseRotation 0 0 0 = 1 := by
  simp [phaseRotation]

example : phaseRotation 0 0 1 = 0 := by
  simp [phaseRotation]

example : fourPhaseAverage 0 = 0 := by
  simp [fourPhaseAverage]

example (a b c1 c2 : ℝ) : phaseSymmetricMatrix a b c1 c2 0 3 = c1 := by
  rfl

example (a b c1 c2 : ℝ) : phaseSymmetricMatrix a b c1 c2 1 3 = -c2 := by
  rfl

end QAlgorithms.Papers.Independent.Advance50.P42


