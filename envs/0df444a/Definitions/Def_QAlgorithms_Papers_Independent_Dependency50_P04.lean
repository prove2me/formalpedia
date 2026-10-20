-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P04
-- name    : QAlgorithms_Papers_Independent_Dependency50_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:18:28.616659+00:00
-- url     : https://prove2.me/theorems/9f1a8140-1780-4d65-b6d0-c2890989eb18
-- title:
--   Definitions for Fundamental Limits of Repeaterless Quantum Communications
-- statement:
--   The objects the formalized statements of *Fundamental Limits of Repeaterless Quantum Communications* (arXiv:1510.08863) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `teleportationUnitary`: PDF p.13, Eqs.(71)--(73): the teleportation matrix X^a Z^b in the computational basis. X shifts j to j+a modulo d and Z has positive phase. The declarations using this matrix require positive input dimension.
--   - `IsTeleportationCovariant`: PDF p.3, Eq.(9), and pp.13--14: for each teleportation matrix the output correction is one unitary valid for every normalized input state. The input and output dimensions may differ.
-- source:
--   Fundamental Limits of Repeaterless Quantum Communications, arXiv:1510.08863v8, https://arxiv.org/abs/1510.08863v8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
# Fundamental Limits of Repeaterless Quantum Communications

arXiv:1510.08863v8. This draft states the finite-dimensional Choi commutator
criterion. All other inventory nodes have explicit entries in the unit's HARD.md
and GAPS.json. In particular no unrestricted operational capacity is represented
by an unconstrained scalar or by a finite-dimensional surrogate.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P04

/-- PDF p.13, Eqs.(71)--(73): the teleportation matrix X^a Z^b in the
computational basis. X shifts j to j+a modulo d and Z has positive phase.
The declarations using this matrix require positive input dimension. -/
def teleportationUnitary (d : ℕ) (a b : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val = (j.val + a.val) % d then
    Complex.exp (((2 * Real.pi * (b.val : ℝ) * (j.val : ℝ) / (d : ℝ) : ℝ) : ℂ) *
      Complex.I)
  else 0

/-- PDF p.3, Eq.(9), and pp.13--14: for each teleportation matrix the
output correction is one unitary valid for every normalized input state.
The input and output dimensions may differ. -/
def IsTeleportationCovariant {d e : ℕ}
    (Phi : QAlgorithms.Superop (Fin d) (Fin e)) : Prop :=
  ∀ a b : Fin d, ∃ V : Matrix.unitaryGroup (Fin e) ℂ,
    ∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
      Phi (teleportationUnitary d a b * rho * (teleportationUnitary d a b)ᴴ) =
        (V : Matrix (Fin e) (Fin e) ℂ) * Phi rho *
          (V : Matrix (Fin e) (Fin e) ℂ)ᴴ

/-- The shift convention sends |0> to |1> in dimension two. -/
example : teleportationUnitary 2 1 0 1 0 = 1 := by
  norm_num [teleportationUnitary]

/-- The same shift has zero |0><0| matrix element. -/
example : teleportationUnitary 2 1 0 0 0 = 0 := by
  norm_num [teleportationUnitary]

/-- The identity channel's Bell coherence has the normalized value 1/2. -/
example : QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi (fun rho : Matrix (Fin 2) (Fin 2) ℂ => rho)
    (0, 0) (1, 1) = (1 / 2 : ℂ) := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi, Matrix.single]

/-- Reference precedes output, including when the dimensions differ. -/
example {d e : ℕ} (Phi : QAlgorithms.Superop (Fin d) (Fin e))
    (i j : Fin d) (b c : Fin e) :
    QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi (i, b) (j, c) = Phi (Matrix.single i j 1) b c / (d : ℂ) := by
  simp [QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi]

end QAlgorithms.Papers.Independent.Dependency50.P04


