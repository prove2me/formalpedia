-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_SquareIntegrableConj
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_SquareIntegrableConj
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:31.664335+00:00
-- url     : https://prove2.me/theorems/728833cc-6790-4a56-98c6-7db1b22fc2c5
-- title:
--   Square Integrable Conj
-- statement:
--   Definitions and structural lemmas for Square Integrable Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/SquareIntegrableConj.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
import Theorems.Thm_PI_ZuckTensorWork_revE_revE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.ZuckTensorWork.Cj.mk_un
attribute [local simp] PI.ZuckTensorWork.Cj.un_mk


set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
namespace SqInt
variable {n : ℕ}
theorem revM_mul (A B : Matrix (Fin n) (Fin n) ℂ) : revM (A * B) = revM A * revM B := by
  unfold revM
  exact (Matrix.submatrix_mul_equiv A B Fin.rev Fin.revPerm Fin.rev).symm
theorem revM_one : revM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  simp [revM, Matrix.one_apply]
theorem revM_revM (A : Matrix (Fin n) (Fin n) ℂ) : revM (revM A) = A := by
  ext i j
  simp [revM]
theorem revM_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) : revM Aᴴ = (revM A)ᴴ := by
  unfold revM
  exact (Matrix.conjTranspose_submatrix A Fin.rev Fin.rev).symm
theorem revM_Jm (ε : Fin n → Bool) : revM (Jm ε) = Jm (revE ε) := by
  unfold revM Jm revE
  exact Matrix.submatrix_diagonal _ Fin.rev Fin.rev_injective
theorem inUJ_rev (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (h : inUJ ε g) :
    inUJ (revE ε) (revM g) := by
  unfold inUJ at *
  rw [← revM_Jm, ← revM_conjTranspose, ← revM_mul, ← revM_mul, h]
def revHom : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun := revM
  map_one' := revM_one
  map_mul' := revM_mul
theorem mem_fwd (ε : Fin n → Bool) (g : UJ (revE ε)) :
    Units.map (revHom (n := n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ UJ ε := by
  show inUJ ε (revM (umat g))
  have h := inUJ_rev (revE ε) (g.2 : inUJ (revE ε) (umat g))
  rwa [revE_revE] at h
theorem mem_bwd (ε : Fin n → Bool) (g : UJ ε) :
    Units.map (revHom (n := n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ UJ (revE ε) := by
  show inUJ (revE ε) (revM (umat g))
  exact inUJ_rev ε (g.2 : inUJ ε (umat g))
def phiE (ε : Fin n → Bool) : UJ (revE ε) ≃* UJ ε where
  toFun g := ⟨Units.map revHom (g : (Matrix (Fin n) (Fin n) ℂ)ˣ), mem_fwd ε g⟩
  invFun g := ⟨Units.map revHom (g : (Matrix (Fin n) (Fin n) ℂ)ˣ), mem_bwd ε g⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    exact revM_revM (umat g)
  right_inv g := by
    apply Subtype.ext; apply Units.ext
    exact revM_revM (umat g)
  map_mul' g h := by
    apply Subtype.ext; apply Units.ext
    exact revM_mul (umat g) (umat h)
end SqInt
end PI.ZuckTensorWork
end


