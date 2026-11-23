-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:08.585317+00:00
-- url     : https://prove2.me/theorems/7222e331-7d20-48c5-b588-7bf11f919c1c
-- title:
--   Prod Cast LESucc
-- statement:
--   Definitions and structural lemmas for Prod Cast LESucc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ProdCastLESucc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
section Mat
variable {n : ℕ}
end Mat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def uOf (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := uMat (gram τ.1 X.Gm (mat x τ))
def dOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := gram τ.1 X.Gm (mat x τ * uOf X x τ) k k
def sOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := ((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ)
def bOf (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix _ _ ℂ)
end
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData


