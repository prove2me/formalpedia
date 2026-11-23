-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:42.02148+00:00
-- url     : https://prove2.me/theorems/0c46ba24-fcb0-4eba-9421-efde029d4999
-- title:
--   Bf Sub Right
-- statement:
--   Definitions and structural lemmas for Bf Sub Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def Bf (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) : ℂ := ∑ a, ∑ b, v a * Gp X Z τ a b * conj (w b)
def Nv (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (m : Fin (r - X.p0)) : ℂ :=
  v (nI X m) + ∑ c, Z τ m c * v (Fin.castLE X.p0_le c)
def Pv (v : Fin r → ℂ) (a : Fin X.p0) : ℂ := v (Fin.castLE X.p0_le a)
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds


