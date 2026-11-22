-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:24.316243+00:00
-- url     : https://prove2.me/theorems/b6b1dfd8-c44c-442c-8a7e-f626f35bee8e
-- title:
--   Qc Col ESymm Val
-- statement:
--   Definitions and structural lemmas for Qc Col ESymm Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColESymmVal.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
def qc_sh {n : ℕ} (mu : Fin n → ℤ) (ε : ℤ) : Fin n → ℤ := fun a => mu a + ε
lemma qc_colH_sh {n : ℕ} (mu : Fin n → ℤ) (ε c : ℤ) : colH (qc_sh mu ε) (c + ε) = colH mu c := by
  unfold colH qc_sh
  congr 1
  ext m
  simp
lemma qc_mem_sh (mu : Fin n → ℤ) (ε c : ℤ) : c + ε ∈ TCols (qc_sh mu ε) ↔ c ∈ TCols mu := by
  simp [TCols, qc_sh]
def qc_colE (mu : Fin n → ℤ) (ε : ℤ) : ↥(TCols mu) ≃ ↥(TCols (qc_sh mu ε)) where
  toFun c := ⟨c.1 + ε, (qc_mem_sh mu ε c.1).2 c.2⟩
  invFun c := ⟨c.1 - ε, (qc_mem_sh mu ε _).1 (by rw [sub_add_cancel]; exact c.2)⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)
def qc_idxE (mu : Fin n → ℤ) (ε : ℤ) : TIdx (qc_sh mu ε) ≃ TIdx mu where
  toFun I c := ⟨(I (qc_colE mu ε c)).1, (I (qc_colE mu ε c)).2.trans (qc_colH_sh mu ε c.1)⟩
  invFun I c := ⟨(I ((qc_colE mu ε).symm c)).1, (I ((qc_colE mu ε).symm c)).2.trans (by
    have := qc_colH_sh mu ε (c.1 - ε)
    rw [sub_add_cancel] at this
    exact this.symm)⟩
  left_inv I := by
    funext c
    apply Subtype.ext
    show (I (qc_colE mu ε ((qc_colE mu ε).symm c))).1 = (I c).1
    rw [Equiv.apply_symm_apply]
  right_inv I := by
    funext c
    apply Subtype.ext
    show (I ((qc_colE mu ε).symm (qc_colE mu ε c))).1 = (I c).1
    rw [Equiv.symm_apply_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies


