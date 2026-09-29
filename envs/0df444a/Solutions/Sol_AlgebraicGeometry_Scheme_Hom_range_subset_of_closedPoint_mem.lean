-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8e71fc8f-85fa-5c40-9619-ae9ffaba2d6c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom Spec Scheme" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom Opens" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "continuous" end AlgebraicGeometry.Scheme.Hom
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in
theorem AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW

theorem solution
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) :=
  AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux W σ hW

end S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem (solution)
