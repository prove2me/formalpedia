-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:40.439279+00:00
-- url     : https://prove2.me/theorems/92fa0ea6-e79d-41b7-a4dc-76a5d904f3c3
-- title:
--   Exhaust FStatement Pf C
-- statement:
--   Definitions and structural lemmas for Exhaust FStatement Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustFStatementPfC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def nM (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := mat (nmat X z) τ
def qI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩
def n1 (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (nM X z τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)
def Wm (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  (nM X z τ).submatrix (qI X) (Fin.castLE X.p0_le)
def Zt (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin (r - X.p0)) ℂ :=
  (Wm X z τ * (n1 X z τ)⁻¹)ᵀ
def Am (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ := 1 - Zt X z τ * (Zt X z τ)ᴴ
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF


