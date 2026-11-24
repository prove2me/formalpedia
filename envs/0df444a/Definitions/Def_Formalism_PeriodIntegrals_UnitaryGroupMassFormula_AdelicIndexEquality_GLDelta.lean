-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:16.004983+00:00
-- url     : https://prove2.me/theorems/dce79b09-63dd-4c19-b413-2c8574cf73cf
-- title:
--   GLDelta
-- statement:
--   Definitions and structural lemmas for GLDelta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
namespace GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
def glOf (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  ⟨M, M⁻¹, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr h),
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr h)⟩
def dU : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom
theorem perm_conj (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (M : Matrix (Fin n) (Fin n) k) :
    σ.toPEquiv.toMatrix * M * σ.toPEquiv.toMatrix = M.submatrix σ σ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]
  rfl
theorem perm_sq (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) :
    σ.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin n) (Fin n) k) := by
  have e := perm_conj σ hσ (1 : Matrix (Fin n) (Fin n) k)
  rwa [Matrix.mul_one, Matrix.submatrix_one_equiv] at e
def sU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, perm_sq σ hσ, perm_sq σ hσ⟩
end GLChiPf
end PI.UnitaryGroupMassFormula.AdIndexEq


