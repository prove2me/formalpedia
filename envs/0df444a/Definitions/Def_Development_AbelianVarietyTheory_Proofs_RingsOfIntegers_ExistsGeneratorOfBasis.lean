-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
-- name    : Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:58.378583+00:00
-- url     : https://prove2.me/theorems/b2b285dd-0299-44ad-95c4-2aa802eaf7cf
-- title:
--   Exists Generator Of Basis
-- statement:
--   Definitions and structural lemmas for Exists Generator Of Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsGeneratorOfBasis.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndivisibleSection
section Calc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
def smulSec {M : LB Y} (c : Γ(Y, ⊤)) (t : LB.Sec M) : LB.Sec M where
  f j := resTop _ c * t.f j
  compat i j := by
    have e : ∀ {W W' : Y.Opens} (h : W' ≤ W),
        (Y.presheaf.map (homOfLE h).op).hom (resTop W c) = resTop W' c := fun h => by
      rw [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, t.compat i j, e, e]
    ring
end Calc
section Deg
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
end Deg
end GlobalTheory.IndivisibleSection


