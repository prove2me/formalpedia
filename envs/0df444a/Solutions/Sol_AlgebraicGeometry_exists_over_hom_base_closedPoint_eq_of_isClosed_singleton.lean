-- Prove2me | solution 1 for AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9667dbdb-31e9-5948-9058-32f2067b01e7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t, z.left.base (IsLocalRing.closedPoint k) = x := by
  refine ⟨Over.homMk (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ?_, ?_⟩
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ≫ t = 𝟙 _
    rw [Category.assoc, ← SpecMap_residueFieldIsoBase_inv t x hx, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) = x
    have hmem : (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) ∈ Set.range (X.fromSpecResidueField x).base :=
      ⟨(Spec.map (residueFieldIsoBase t x hx).hom).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem

end S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton (solution)
