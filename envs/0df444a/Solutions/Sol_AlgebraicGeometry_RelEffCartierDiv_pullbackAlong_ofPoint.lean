-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_ofPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8f4b609a-5a78-57e4-8895-64033a37789b

import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.Hom Scheme Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsSeparated Scheme.IdealSheafData graphOver graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver isPullback_mapOnProdOver"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "ofPoint ext pullbackAlong"
namespace OfPointNaturality
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.AlgebraicGeometry.RelEffCartierDiv"

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

theorem isPullback_graphOver_comp [IsSeparated f] (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])) φ
      (mapOnProdOver f φ hφ) (graphOver f a ha) := by
  have s : IsPullback (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) ≫ pullback.snd f g)
      φ φ (graphOver f a ha ≫ pullback.snd f g') := by
    rw [graphOver_snd, graphOver_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine IsPullback.of_right s ?_ (isPullback_mapOnProdOver f φ hφ).flip
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by
  refine RelEffCartierDiv.ext ?_
  change (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) = (graphOver f (φ ≫ a) _).ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (AlgebraicGeometry.RelEffCartierDiv.OfPointNaturality.isPullback_graphOver_comp
      f a ha φ hφ).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint (solution)
