-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:43.081742+00:00
-- url     : https://prove2.me/theorems/e7f81123-14b1-4ed5-b2dc-4c384885017c
-- title:
--   Lift OUnique
-- statement:
--   Definitions and structural lemmas for Lift OUnique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LiftOUnique.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
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
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
def gtφO (m : TO hϖ hv ⟶ D.toPre.P.A) (χ : D.toPre.X) : Fin 4 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(cP D.toPre _ χ * m).left, (cP D.toPre _ χ).left, m.left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left]
def lineφO (m : TO hϖ hv ⟶ D.toPre.P.A) : Fin 2 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(1 : TO hϖ hv ⟶ D.toPre.P.A).left, m.left]
def trO (m : TO hϖ hv ⟶ D.toPre.P.A) : TO hϖ hv ⊗ D.toPre.P.A ⟶ TO hϖ hv ⊗ D.toPre.P.A :=
  lift (fst _ _) (padd D.toPre.P.A (snd _ _) (fst _ _ ≫ m))
end ReciprocityTheory.ChartRestriction.G.DVR.TWM


