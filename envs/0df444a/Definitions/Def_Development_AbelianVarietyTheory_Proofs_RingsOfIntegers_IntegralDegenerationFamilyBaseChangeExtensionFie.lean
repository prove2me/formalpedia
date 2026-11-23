-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
-- name    : Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:56.961723+00:00
-- url     : https://prove2.me/theorems/2309d88b-f854-4003-829f-dcde16bf6f9b
-- title:
--   Integral Degeneration Family Base Change Extension Fie
-- statement:
--   Definitions and structural lemmas for Integral Degeneration Family Base Change Extension Fie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralDegenerationFamilyBaseChangeExtensionFie.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FamBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
theorem comp_jFK_self : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
    jFK (R := R) (FractionRing R) = jFK (R := R) F := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = 𝟙 _ := Spec.map_id _
  exact (congrArg (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ ·) e).trans (Category.comp_id _)
noncomputable def toGen : TF (R := R) F ⟶ TF (R := R) (FractionRing R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK_self F)))
noncomputable def bc : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) :=
  lift (fst _ _ ≫ toGen F) (DegPre.prB D F)
end GlobalTheory.FamBaseChange


