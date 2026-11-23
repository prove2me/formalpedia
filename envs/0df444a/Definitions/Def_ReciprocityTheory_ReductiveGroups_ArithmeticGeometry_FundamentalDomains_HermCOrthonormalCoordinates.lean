-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:37.300785+00:00
-- url     : https://prove2.me/theorems/478ff7bf-b8c6-4857-981c-d16df30d9c16
-- title:
--   Herm COrthonormal Coordinates
-- statement:
--   Definitions and structural lemmas for Herm COrthonormal Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
def mjip {n : ℕ} (p q : Fin n → ℂ) : ℂ := ∑ i, p i * conj (q i)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def mjpa (w : Fin r → ℂ) : Fin X.p0 → ℂ := fun a => w (Fin.castLE X.p0_le a)
def mjpb (w : Fin r → ℂ) : Fin (r - X.p0) → ℂ := fun m => w (nI X m)
def mjg (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) : Fin r → ℂ :=
  ∑ c, δ c • col (X.lowBlock Z τ) (Fin.castLE X.p0_le c)
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds


