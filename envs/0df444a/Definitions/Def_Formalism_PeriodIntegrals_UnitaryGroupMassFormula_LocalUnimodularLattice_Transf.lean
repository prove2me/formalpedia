-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:16.59908+00:00
-- url     : https://prove2.me/theorems/89afc3cf-af0a-42c3-842a-67d1a5a1eced
-- title:
--   Transf
-- statement:
--   Definitions and structural lemmas for Transf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/Transf.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
noncomputable section
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.TR
open PI Formalism.REAL
variable {m : ℕ}
def conjH (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1) : MtM m ≃ₜ MtM m where
  toFun x := fun i j => (Q * Matrix.of x * P) i j
  invFun x := fun i j => (P * Matrix.of x * Q) i j
  left_inv x := by
    funext i j
    show (P * (Q * Matrix.of x * P) * Q) i j = x i j
    rw [show P * (Q * Matrix.of x * P) * Q = (P * Q) * Matrix.of x * (P * Q) by
      simp only [Matrix.mul_assoc], hPQ, Matrix.one_mul, Matrix.mul_one]
    rfl
  right_inv x := by
    funext i j
    show (Q * (P * Matrix.of x * Q) * P) i j = x i j
    rw [show Q * (P * Matrix.of x * Q) * P = (Q * P) * Matrix.of x * (Q * P) by
      simp only [Matrix.mul_assoc], hQP, Matrix.one_mul, Matrix.mul_one]
    rfl
  continuous_toFun := by
    show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => Q * x * P
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    show Continuous fun x : Matrix (Fin m) (Fin m) ℂ => P * x * Q
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
end PI.NUnimodLoc.UnitaryGroupMassFormula.TR


