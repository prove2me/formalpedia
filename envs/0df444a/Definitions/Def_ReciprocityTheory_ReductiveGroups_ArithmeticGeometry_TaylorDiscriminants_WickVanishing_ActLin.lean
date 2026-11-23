-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:26.504951+00:00
-- url     : https://prove2.me/theorems/a0bbdc3a-31fa-4a48-ba48-693e2ffd7145
-- title:
--   Act Lin
-- statement:
--   Definitions and structural lemmas for Act Lin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ActLin.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
def ActLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O)
    (ℓ ε : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (B.G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    IsInvPair ε ℓ → ∀ (a : O) (i : Fin d),
      comp1 ℓ (comp1 (B.A.act a) ε) i = ∑ j, C (dLin (B.A.act a) i j) * X ((0 : Fin 1), j)
namespace WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
end WickVanishing
end ReciprocityTheory.ChartRestriction.G.TB


