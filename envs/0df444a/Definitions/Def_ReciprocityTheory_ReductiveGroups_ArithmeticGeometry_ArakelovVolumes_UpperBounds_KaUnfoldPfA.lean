-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:51.818855+00:00
-- url     : https://prove2.me/theorems/6113d9ef-9e7e-4864-88e3-63a6d3e35961
-- title:
--   Ka Unfold Pf A
-- statement:
--   Definitions and structural lemmas for Ka Unfold Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
section
def Yb {p q : ℕ} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  M.toBlocks₁₂ * M.toBlocks₂₂⁻¹
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def eT (X : Data E r) : Fin (r - X.p0) ⊕ Fin X.p0 ≃ Fin r :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by have := X.p0_le; omega)))
def tl (X : Data E r) (M : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ := M.submatrix (eT X) (eT X)
def Mx (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  tl X ((mat x0 τ)⁻¹ * mat x τ)
def kap (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, dpow (Yb (Mx X x0 x τ)) bb
def gm (X : Data E r) (x0 : Frame X.Ψ r) (γ : GL (Fin r) E) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  tl X ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ)
end
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU


