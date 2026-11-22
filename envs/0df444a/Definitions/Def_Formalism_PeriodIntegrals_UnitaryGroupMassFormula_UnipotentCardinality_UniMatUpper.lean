-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:14.823333+00:00
-- url     : https://prove2.me/theorems/08d7b826-1e96-405c-ae28-7cf33a4fb383
-- title:
--   Uni Mat Upper
-- statement:
--   Definitions and structural lemmas for Uni Mat Upper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCardinality/UniMatUpper.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.GGCardUniWork
open Finset Matrix Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
abbrev Pairs (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}
def uniMat (f : Pairs k → F) : Matrix (Fin k) (Fin k) F :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0
theorem uniMat_upper (f : Pairs k → F) : (uniMat f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [uniMat, ne_of_gt hji, not_lt.mpr hji.le]
theorem uniMat_det (f : Pairs k → F) : (uniMat f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (uniMat_upper f)]
  simp [uniMat]
noncomputable def uniGL (f : Pairs k → F) : GL (Fin k) F :=
  GeneralLinearGroup.mkOfDetNeZero (uniMat f) (by rw [uniMat_det]; exact one_ne_zero)
theorem uniGL_coe (f : Pairs k → F) : ((uniGL f : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = uniMat f := rfl
theorem isUni_uniGL (f : Pairs k → F) : IsUni k (uniGL f) := by
  unfold IsUni
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · simp [uniGL_coe, uniMat]
  · simp [uniGL_coe, uniMat, ne_of_gt h, not_lt.mpr h.le]
noncomputable def uniEquiv : {x : GL (Fin k) F // IsUni k x} ≃ (Pairs k → F) where
  toFun x p := (x.1 : Matrix (Fin k) (Fin k) F) p.1.1 p.1.2
  invFun f := ⟨uniGL f, isUni_uniGL f⟩
  left_inv x := by
    obtain ⟨x, hd, hl⟩ := x
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    simp only [uniGL_coe, uniMat]
    by_cases h : i = j
    · subst h; simp [hd i]
    · by_cases h' : i < j
      · simp [h, h']
      · have : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
        simp [h, h', hl i j this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h1 : i ≠ j := ne_of_lt h
    simp [uniGL_coe, uniMat, h1, h]
end PI.GGCardUniWork


