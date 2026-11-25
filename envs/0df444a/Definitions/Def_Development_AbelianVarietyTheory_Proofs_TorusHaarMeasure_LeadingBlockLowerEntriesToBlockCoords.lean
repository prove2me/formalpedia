-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:14:56.867038+00:00
-- url     : https://prove2.me/theorems/6e66c3b3-1a6a-4692-9bda-65b62c011db7
-- title:
--   Leading Block Lower Entries To Block Coords
-- statement:
--   Definitions and structural lemmas for Leading Block Lower Entries To Block Coords, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeadingBlockLowerEntriesToBlockCoords.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_unipotentFrame_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_nM_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_sum_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_sum_split
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
namespace GlobalTheory.UpCoordCompare
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def coordOf (x : Frame X.Ψ r) : V (nd X) := WithLp.toLp 2 fun i =>
  x ((Fintype.equivFin (Ent X)).symm i).1 ((Fintype.equivFin (Ent X)).symm i).2.1.1
    ((Fintype.equivFin (Ent X)).symm i).2.1.2
theorem nmat_coordOf_of_lt (x : Frame X.Ψ r) (τ : X.Ψ) {a b : Fin r} (h : b < a) :
    nmat X (coordOf X x) τ a b = x τ a b := by
  simp [nmat, h, coordOf]
theorem nmat_of_not_lt (z w : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : ¬ b < a) :
    nmat X z τ a b = nmat X w τ a b := by
  simp [nmat, h]
theorem nmat_apply_idx (z : V (nd X)) (i : Fin (nd X)) :
    nmat X z ((Fintype.equivFin (Ent X)).symm i).1 ((Fintype.equivFin (Ent X)).symm i).2.1.1
      ((Fintype.equivFin (Ent X)).symm i).2.1.2 = z i := by
  have h := ((Fintype.equivFin (Ent X)).symm i).2.2
  simp only [nmat, dif_pos h]
  exact congrArg (fun j => z j) ((Fintype.equivFin (Ent X)).apply_symm_apply i)
theorem coordOf_nmat (z : V (nd X)) : coordOf X (nmat X z) = z := by
  ext i
  exact nmat_apply_idx X z i
theorem nFrame_apply (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    nFrame X z τ a b = if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      ∑ c : Fin r, if (c : ℕ) < X.p0 then nmat X z τ a c * nmat X z τ c b else 0
    else nmat X z τ a b := by
  show ∑ c, zFrame X z τ a c * leviFrame X z τ c b = _
  simp only [zFrame, leviFrame]
  by_cases ha : X.p0 ≤ (a : ℕ)
  · by_cases hb : (b : ℕ) < X.p0
    · rw [if_pos ⟨ha, hb⟩]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : (c : ℕ) < X.p0
      · have : ¬ X.p0 ≤ (c : ℕ) := by omega
        simp [ha, hb, hc, this]
      · have : X.p0 ≤ (c : ℕ) := by omega
        simp [ha, hb, hc, this]
    · rw [if_neg (fun h => hb h.2), Finset.sum_eq_single a]
      · have : ¬ (a : ℕ) < X.p0 := by omega
        simp [hb, this]
      · intro c _ hca
        by_cases hc : (c : ℕ) < X.p0
        · have h1 : c < b := Fin.lt_def.2 (by omega)
          have h2 : nmat X z τ c b = 0 := ExF.nM_upper X z τ h1
          simp [hb, h2]
        · simp [hc, hca.symm]
      · simp
  · rw [if_neg (fun h => ha h.1), Finset.sum_eq_single a]
    · simp [ha]
    · intro c _ hca
      simp [ha, hca.symm]
    · simp
def toEntries (z : V (nd X)) : V (nd X) := coordOf X (nFrame X z)
def ofEntries (w : V (nd X)) : V (nd X) := coordOf X fun τ a b =>
  if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
    ExF.Zt X w τ ⟨b, h.2⟩ ⟨a - X.p0, by have := a.isLt; omega⟩
  else nmat X w τ a b
theorem nmat_toEntries (z : V (nd X)) : nmat X (toEntries X z) = nFrame X z := by
  funext τ a b
  by_cases h : b < a
  · exact nmat_coordOf_of_lt X _ τ h
  · have : ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0) := fun h' => h (Fin.lt_def.2 (by omega))
    rw [nFrame_apply, if_neg this]
    exact nmat_of_not_lt X _ _ τ h
theorem nmat_toEntries_of_not (z : V (nd X)) (τ : X.Ψ) {a b : Fin r}
    (h : ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0)) : nmat X (toEntries X z) τ a b = nmat X z τ a b := by
  rw [nmat_toEntries, nFrame_apply, if_neg h]
theorem nmat_ofEntries_of_not (w : V (nd X)) (τ : X.Ψ) {a b : Fin r}
    (h : ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0)) : nmat X (ofEntries X w) τ a b = nmat X w τ a b := by
  by_cases h' : b < a
  · rw [ofEntries, nmat_coordOf_of_lt X _ τ h', dif_neg h]
  · exact nmat_of_not_lt X _ _ τ h'
theorem leadingBlock_blockCoordsToLowerEntries (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (toEntries X z) τ = ExF.n1 X z τ := by
  ext a b
  refine nmat_toEntries_of_not X z τ fun h => ?_
  have := a.isLt; have h1 : X.p0 ≤ (a : ℕ) := h.1; omega
theorem leadingBlock_lowerEntriesToBlockCoords (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (ofEntries X z) τ = ExF.n1 X z τ := by
  ext a b
  refine nmat_ofEntries_of_not X z τ fun h => ?_
  have := a.isLt; have h1 : X.p0 ≤ (a : ℕ) := h.1; omega
theorem Wm_toEntries (z : V (nd X)) (τ : X.Ψ) :
    ExF.Wm X (toEntries X z) τ = ExF.Wm X z τ * ExF.n1 X z τ := by
  ext m b
  show nmat X (toEntries X z) τ (ExF.qI X m) (Fin.castLE X.p0_le b) = _
  have h : X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 :=
    ⟨Nat.le_add_right _ _, b.isLt⟩
  rw [nmat_toEntries, nFrame_apply, if_pos h, ExF.sum_split X, Matrix.mul_apply]
  have h2 : ∀ k : Fin (r - X.p0), ¬ ((ExF.qI X k : Fin r) : ℕ) < X.p0 := fun k =>
    not_lt.2 (Nat.le_add_right _ _)
  simp only [h2, if_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [if_pos (show ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 from c.isLt)]
  rfl
theorem Wm_ofEntries (w : V (nd X)) (τ : X.Ψ) :
    ExF.Wm X (ofEntries X w) τ = ExF.Wm X w τ * (ExF.n1 X w τ)⁻¹ := by
  ext m b
  show nmat X (ofEntries X w) τ (ExF.qI X m) (Fin.castLE X.p0_le b) = _
  have h : X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 :=
    ⟨Nat.le_add_right _ _, b.isLt⟩
  rw [ofEntries, nmat_coordOf_of_lt X _ τ (Fin.lt_def.2 (by omega)), dif_pos h]
  have : (⟨(ExF.qI X m : ℕ) - X.p0, by have := (ExF.qI X m).isLt; omega⟩ : Fin (r - X.p0)) = m :=
    Fin.ext (by simp [ExF.qI])
  rw [this]
  rfl
theorem ext_blocks {z w : V (nd X)}
    (h1 : ∀ τ (a b : Fin r), ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0) → nmat X z τ a b = nmat X w τ a b)
    (h2 : ∀ τ, ExF.Wm X z τ = ExF.Wm X w τ) : z = w := by
  rw [← coordOf_nmat X z, ← coordOf_nmat X w]
  congr 1
  funext τ a b
  by_cases h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0
  · have := congrFun (congrFun (h2 τ) ⟨a - X.p0, by have := a.isLt; omega⟩) ⟨b, h.2⟩
    have e : ExF.qI X ⟨a - X.p0, by have := a.isLt; omega⟩ = a := Fin.ext (by simp [ExF.qI]; omega)
    simp only [ExF.Wm, Matrix.submatrix_apply, e] at this
    exact this
  · exact h1 τ a b h
theorem isUnit_det_leadingBlock_lowerEntries (z : V (nd X)) (τ : X.Ψ) : IsUnit (ExF.n1 X z τ).det := by
  rw [ExF.det_unipotentFrame_eq_one]; exact isUnit_one
def coordEquiv : V (nd X) ≃ V (nd X) where
  toFun := toEntries X
  invFun := ofEntries X
  left_inv z := ext_blocks X
    (fun τ a b h => by rw [nmat_ofEntries_of_not X _ τ h, nmat_toEntries_of_not X _ τ h])
    (fun τ => by
      rw [Wm_ofEntries, Wm_toEntries, leadingBlock_blockCoordsToLowerEntries, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_leadingBlock_lowerEntries X z τ)])
  right_inv z := ext_blocks X
    (fun τ a b h => by rw [nmat_toEntries_of_not X _ τ h, nmat_ofEntries_of_not X _ τ h])
    (fun τ => by
      rw [Wm_toEntries, Wm_ofEntries, leadingBlock_lowerEntriesToBlockCoords, Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_det_leadingBlock_lowerEntries X z τ)])
def lowEquiv : Fin X.p0 ≃ {b : Fin r // (b : ℕ) < X.p0} where
  toFun c := ⟨Fin.castLE X.p0_le c, c.isLt⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def highEquiv : Fin (r - X.p0) ≃ {a : Fin r // X.p0 ≤ (a : ℕ)} where
  toFun m := ⟨ExF.qI X m, Nat.le_add_right _ _⟩
  invFun a := ⟨a.1 - X.p0, by have := a.1.isLt; have := a.2; omega⟩
  left_inv m := Fin.ext (by simp [ExF.qI])
  right_inv a := Subtype.ext (Fin.ext (by have := a.2; simp [ExF.qI]; omega))
end
end GlobalTheory.UpCoordCompare


