-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:59.342798+00:00
-- url     : https://prove2.me/theorems/ae0fe80e-fd09-46f4-87e6-b43756027860
-- title:
--   Ka Unfold Pf B
-- statement:
--   Definitions and structural lemmas for Ka Unfold Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_det_ne_of_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_mul
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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def untl (X : Data E r) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := M.submatrix (eT X).symm (eT X).symm
theorem tl_one (X : Data E r) : tl X (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  rw [tl, Matrix.submatrix_one_equiv]
theorem gm_mul (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ γ' : GL (Fin r) E) (τ : X.Ψ) :
    gm X x0 (γ * γ') τ = gm X x0 γ τ * gm X x0 γ' τ := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, gm, gm, ← tl_mul]
  congr 1
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mat x0 τ) (mat x0 τ)⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
theorem gm_one (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    gm X x0 1 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.nonsing_inv_mul _ hu, tl_one]
def rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    GL (Fin r) E →* (Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) where
  toFun γ k := ⟨gm X x0 γ ((Fintype.equivFin X.Ψ).symm k), gm X x0 γ⁻¹ ((Fintype.equivFin X.Ψ).symm k),
    by rw [← gm_mul X ho, mul_inv_cancel, gm_one X ho],
    by rw [← gm_mul X ho, inv_mul_cancel, gm_one X ho]⟩
  map_one' := by funext k; exact Units.ext (gm_one X ho _)
  map_mul' γ γ' := by funext k; exact Units.ext (gm_mul X ho γ γ' _)
end
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def Phi (X : Data E r) (x0 : Frame X.Ψ r)
    (g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Frame X.Ψ r :=
  fun τ => (mat x0 τ * untl X (g (Fintype.equivFin X.Ψ τ)).val : Matrix (Fin r) (Fin r) ℂ)
def vpt (X : Data E r) (z : V (nd X)) : V (nD (Fintype.card X.Ψ) (r - X.p0) X.p0) :=
  WithLp.toLp 2 fun i =>
    (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm (finProdFinEquiv.symm i).1))ᵀ
      (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2
end
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU


