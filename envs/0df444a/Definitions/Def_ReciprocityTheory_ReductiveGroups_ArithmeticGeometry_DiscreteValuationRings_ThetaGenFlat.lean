-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:54.124903+00:00
-- url     : https://prove2.me/theorems/8351007b-9295-4f46-b3b0-ba32e25480e5
-- title:
--   Theta Gen Flat
-- statement:
--   Definitions and structural lemmas for Theta Gen Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenFlat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
end
end ReciprocityTheory.ChartRestriction.G.DVR.TG
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R]
def toW {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) : R →+* Γ(X, W) :=
  (p.appLE ⊤ W (show W ≤ p ⁻¹ᵁ ⊤ from le_top)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
abbrev tq (J : Ideal R) : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
end
end ReciprocityTheory.ChartRestriction.G.DVR.TG
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R] [IsDomain R]
abbrev jF (R : Type) [CommRing R] [IsDomain R] :
    Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
end
end ReciprocityTheory.ChartRestriction.G.DVR.TG


