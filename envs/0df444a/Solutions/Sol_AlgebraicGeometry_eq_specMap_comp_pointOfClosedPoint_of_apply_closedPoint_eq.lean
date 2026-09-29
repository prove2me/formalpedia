-- Prove2me | solution 1 for AlgebraicGeometry.eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c9673324-fdfa-5168-be9b-115e7170fa13

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] (ι : k →+* K)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = Spec.map (CommRingCat.ofHom ι))
    (x : ↥X) (hx : IsClosed ({x} : Set ↥X)) (hpx : p.base (IsLocalRing.closedPoint K) = x) :
    p = Spec.map (CommRingCat.ofHom ι) ≫ AlgebraicGeometry.pointOfClosedPoint f x hx := by
  subst hpx
  set e := AlgebraicGeometry.residueFieldIsoBase f (p.base (IsLocalRing.closedPoint K)) hx with he
  set φ := X.descResidueField (Scheme.stalkClosedPointTo p) with hφ
  have hdec : Spec.map φ ≫ X.fromSpecResidueField (p.base (IsLocalRing.closedPoint K)) = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X p

  have hφι : φ = e.hom ≫ CommRingCat.ofHom ι := by
    have h1 : Spec.map φ ≫ Spec.map e.inv = Spec.map (CommRingCat.ofHom ι) := by
      rw [AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdec, hp]
    rw [← Spec.map_comp] at h1
    have h2 : e.inv ≫ φ = CommRingCat.ofHom ι := Spec.map_injective h1
    rw [← h2, Iso.hom_inv_id_assoc]
  conv_lhs => rw [← hdec, hφι, Spec.map_comp, Category.assoc]
  rfl

end S_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq
end P2MW
export P2MW.S_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq (solution)
