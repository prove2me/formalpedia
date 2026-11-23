-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:27.130515+00:00
-- url     : https://prove2.me/theorems/0bf440d1-1b83-4871-8a5b-6d1244b7f86d
-- title:
--   Mono Val
-- statement:
--   Definitions and structural lemmas for Mono Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/MonoVal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.TB.MV
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)
def MonoValSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (ι : Type) [Fintype ι] (j : ι → Fin d), Function.Injective j →
    ∀ (α : ι →₀ ℕ) (g : PS k 1 d),
      constantCoeff (DpolyOf (addF k d) (fun l => Pi.single (j l) 1) (MvPolynomial.monomial α 1) g) =
        (∏ l, ((α l).factorial : k)) * coeff (∑ l, α l • Finsupp.single ((0 : Fin 1), j l) 1) g
section Pair
variable {k : Type} [CommRing k] {σ : Type}
end Pair
section Pair2
variable {k : Type} [CommRing k]
end Pair2
end ReciprocityTheory.ChartRestriction.G.TB.MV


