-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:10.524025+00:00
-- url     : https://prove2.me/theorems/21afa01a-34c6-4c61-a14c-a09fcd3d01f7
-- title:
--   Pt Order Prod Sub
-- statement:
--   Definitions and structural lemmas for Pt Order Prod Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
section PowerSeriesAgreement
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
def PTAgree (k : ℕ) (A A' : ι → MvPowerSeries τ R) : Prop :=
  ∀ i (e : τ →₀ ℕ), e.degree < k → coeff e (A i) = coeff e (A' i)
section Fixed
variable (T : (ι → MvPowerSeries τ R) → (ι → MvPowerSeries τ R))
  (P : (ι → MvPowerSeries τ R) → Prop)
end Fixed
section Order
end Order
end PowerSeriesAgreement
end
end ReciprocityTheory.ChartRestriction.G.Sh


