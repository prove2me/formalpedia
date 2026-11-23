-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:09.225796+00:00
-- url     : https://prove2.me/theorems/0fbce071-9d58-4113-8911-2aa655dd9f5a
-- title:
--   Theta Gen Generic
-- statement:
--   Definitions and structural lemmas for Theta Gen Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenGeneric.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
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
def pullSec' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) :
    LB.Sec (LB.LinComb L φ' ε) := by
  have e : φ' = fun k => h ≫ φ k := funext hφ
  subst e
  exact pullSec L φ ε s h
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def secK (U : UnifPre I D A G) (s : H0 U.LG.L 1) : U.SecK 1 :=
  pullSec' U.LG.L _ _ s (pullback.fst G.hom (jK R)) _ (fun _ => (Category.comp_id _).symm)
end ReciprocityTheory.ChartRestriction.G.DVR.TG


