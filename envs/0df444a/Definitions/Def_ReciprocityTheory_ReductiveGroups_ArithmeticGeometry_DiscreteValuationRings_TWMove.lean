-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:26.493172+00:00
-- url     : https://prove2.me/theorems/81d3b17d-f408-4cdd-a382-b6cd1adddfa4
-- title:
--   TWMove
-- statement:
--   Definitions and structural lemmas for TWMove, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TWMove.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO_comp

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
abbrev TO : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (fO v hϖ hv)))
abbrev ιS : TF (R := V) F ⟶ TO hϖ hv :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ Spec.map (CommRingCat.ofHom (fO v hϖ hv)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
abbrev jO : DegPre.BF D.toPre F ⟶ TO hϖ hv ⊗ D.toPre.P.A := ιS hϖ hv ▷ D.toPre.P.A
abbrev ιr (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : F :=
  algebraMap (Ov v) F ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom r)
end ReciprocityTheory.ChartRestriction.G.DVR.TWM


