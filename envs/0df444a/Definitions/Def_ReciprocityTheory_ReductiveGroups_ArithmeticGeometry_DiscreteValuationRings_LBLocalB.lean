-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:43.151988+00:00
-- url     : https://prove2.me/theorems/57d12a01-8b26-4813-98ff-ce893fb43f0c
-- title:
--   LBLocal B
-- statement:
--   Definitions and structural lemmas for LBLocal B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
def scalUnit (c : FractionRing V) (hc : c ≠ 0) : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom.toMonoidHom (Units.mk0 c hc)
lemma sumElim_hφ {X : Scheme.{0}} {Ix Ix' : Type}
    {φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k)
    {φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)} {φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) :
    ∀ k, Sum.elim φ₁' φ₂' k = jK V ≫ Sum.elim φ₁ φ₂ k := by
  rintro (k | k)
  · exact hφ₁ k
  · exact hφ₂ k
end ReciprocityTheory.ChartRestriction.G.DVR


