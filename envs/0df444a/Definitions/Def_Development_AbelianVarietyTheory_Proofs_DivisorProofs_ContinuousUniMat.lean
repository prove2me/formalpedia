-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:28.352822+00:00
-- url     : https://prove2.me/theorems/1346fad9-a07a-46e1-ada6-070b2a74e481
-- title:
--   Continuous Uni Mat
-- statement:
--   Definitions and structural lemmas for Continuous Uni Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousUniMat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal
noncomputable section
namespace GlobalTheory.BorelModulus
abbrev Pos (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem mem_U_iff (g : GL (Fin n) k) :
    g ∈ (borelGL k (Fin n)).U ↔ (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1 := by
  rw [LeviDatum.mem_U]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨fun _ _ hij => h hij, fun i => congrArg (fun t : Fin n → kˣ => (t i : k)) e⟩
  · rintro ⟨h, e⟩
    exact ⟨fun _ _ hij => h _ _ hij, funext fun i => Units.ext (e i)⟩
def uniMat (x : Pos n → k) : Matrix (Fin n) (Fin n) k :=
  fun i j => if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_low (x : Pos n → k) (i j : Fin n) (h : j < i) : uniMat x i j = 0 := by
  simp [uniMat, h.not_gt, h.ne']
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_diag (x : Pos n → k) (i : Fin n) : uniMat x i i = 1 := by
  simp [uniMat]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_det (x : Pos n → k) : (uniMat x).det = 1 := by
  rw [det_of_upperTriangular (fun i j h => uniMat_low x i j h)]
  simp [uniMat_diag]
theorem continuous_uniMat : Continuous (uniMat : (Pos n → k) → _) := by
  refine continuous_matrix fun i j => ?_
  unfold uniMat
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
  · exact continuous_const
def uniGL (x : Pos n → k) : GL (Fin n) k :=
  ⟨uniMat x, (uniMat x).adjugate, by rw [mul_adjugate, uniMat_det, one_smul],
    by rw [adjugate_mul, uniMat_det, one_smul]⟩
theorem continuous_uniGL : Continuous (uniGL : (Pos n → k) → _) :=
  Units.continuous_iff.2 ⟨continuous_uniMat, continuous_uniMat.matrix_adjugate⟩
def coord (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    (borelGL k (Fin n)).U ≃ₜ (Pos n → k) where
  toFun u p := u.1.val p.1.1 p.1.2
  invFun x := ⟨uniGL x, (mem_U_iff _).2 ⟨uniMat_low x, uniMat_diag x⟩⟩
  left_inv u := by
    obtain ⟨h1, h2⟩ := (mem_U_iff _).1 u.2
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    show uniMat (fun p : Pos n => u.1.val p.1.1 p.1.2) i j = u.1.val i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [uniMat, h]
    · rw [uniMat_diag, h2]
    · rw [uniMat_low _ _ _ h, h1 _ _ h]
  right_inv x := by
    funext p
    show uniMat x _ _ = _
    simp [uniMat, p.2]
  continuous_toFun := continuous_pi fun p => (continuous_entry _ _).comp continuous_subtype_val
  continuous_invFun := continuous_uniGL.subtype_mk _
def leftMat (A : Matrix (Fin n) (Fin n) k) : Matrix (Pos n) (Pos n) k :=
  fun p q => if q.1.2 = p.1.2 then A p.1.1 q.1.1 else 0
end GlobalTheory.BorelModulus


