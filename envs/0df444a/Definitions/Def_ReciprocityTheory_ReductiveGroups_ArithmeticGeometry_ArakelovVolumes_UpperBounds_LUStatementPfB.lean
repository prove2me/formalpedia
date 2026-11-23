-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:18.520828+00:00
-- url     : https://prove2.me/theorems/965c7407-a046-4a79-b359-98aa9e16576d
-- title:
--   LUStatement Pf B
-- statement:
--   Definitions and structural lemmas for LUStatement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
noncomputable section
def LowU {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) : Prop := (∀ i k : Fin n, i < k → N i k = 0) ∧ ∀ i, N i i = 1
theorem LowU.det {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (h : LowU N) : N.det = 1 := by
  have hbt : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact h.1 i j (OrderDual.toDual_lt_toDual.mp hij)
  rw [Matrix.det_of_lowerTriangular N hbt]
  simp [h.2]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
def Mx (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat x0 τ)⁻¹ * mat x τ
def DeltaF (x : Frame X.Ψ r) : ℂ := ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k
def nF (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((Lm (Mx X x0 x τ))⁻¹ : Matrix (Fin r) (Fin r) ℂ)
def bF (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (Lm (Mx X x0 x τ) * Mx X x0 x τ : Matrix (Fin r) (Fin r) ℂ)
def zF (x : Frame X.Ψ r) : V (nd X) :=
  WithLp.toLp 2 fun k => nF X x0 x ((Fintype.equivFin (Ent X)).symm k).1
    ((Fintype.equivFin (Ent X)).symm k).2.1.1 ((Fintype.equivFin (Ent X)).symm k).2.1.2
variable {X x0}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf


