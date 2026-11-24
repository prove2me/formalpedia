-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenRank
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:39.530125+00:00
-- url     : https://prove2.me/theorems/1fd50f19-a793-4e61-b240-0804a75594a1
-- title:
--   Theta Gen Rank
-- statement:
--   Definitions and structural lemmas for Theta Gen Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Rel
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
def SecCorr (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (x : LB.Sec (LB.LinComb L φ' ε')) : Prop :=
  ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' → (∀ k k', φ k = φ' k' → j k = j' k') →
    rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s.f j) =
      rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (x.f j')
end Rel
section SameSum
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)
end SameSum
section Rank
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} (D : DegData R I)
end Rank
end ReciprocityTheory.ChartRestriction.G.DVR.TG


