-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c6a3e693-2fe4-511c-82a8-46e3415b0deb

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Spec Spec.map Scheme Smooth Scheme.Hom.stalkMap Scheme.stalkClosedPointTo Spec.map_injective Scheme.Spec_stalkClosedPointTo_fromSpecStalk Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.Hom.germ_stalkMap Spec.fromSpecStalk_eq Scheme.ΓSpecIso Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing"
namespace HenselValue
p2m_open "AlgebraicGeometry"

theorem stalkClosedPointTo_germ_appTop
    {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing A] [Algebra R A]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (σ : Spec (.of A) ⟶ X)
    (hσ : σ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R A))) (r : R) :
    (Scheme.stalkClosedPointTo σ).hom
        ((X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint A)) trivial).hom
          (c.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))) = algebraMap R A r := by

  have key : ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).presheaf.germ ⊤ (c.base (σ.base (IsLocalRing.closedPoint A))) trivial) ≫
      Scheme.Hom.stalkMap c (σ.base (IsLocalRing.closedPoint A)) ≫ Scheme.stalkClosedPointTo σ =
      CommRingCat.ofHom (algebraMap R A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← Spec.fromSpecStalk_eq, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hσ]
  have h := congrArg (fun f => f.hom r) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [← h]
  congr 1

  symm
  rw [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap c ⊤ (σ.base (IsLocalRing.closedPoint A)) trivial]
  rfl

end AlgebraicGeometry.HenselValue

theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [HenselianLocalRing A] [Algebra R A]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [Smooth c]
    (xk : Spec (.of (IsLocalRing.ResidueField A)) ⟶ X)
    (hxk : xk ≫ c = Spec.map (CommRingCat.ofHom ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A)))) :
    ∃ σ : Spec (.of A) ⟶ X,
      σ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))) ≫ σ = xk ∧
      ∀ (r : R) (g : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A))),
        (Scheme.stalkClosedPointTo σ).hom
            ((X.presheaf.germ ⊤ (σ.base (IsLocalRing.closedPoint A)) trivial).hom
              (c.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) * g) =
          algebraMap R A r * (Scheme.stalkClosedPointTo σ).hom g := by
  classical

  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  haveI : Smooth (pullback.snd c g) := inferInstance

  have hcond : xk ≫ c = Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))) ≫ g := by
    rw [hxk, CommRingCat.ofHom_comp, Spec.map_comp]
  let x0 : Spec (.of (IsLocalRing.ResidueField A)) ⟶ pullback c g :=
    pullback.lift xk (Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))) hcond
  have hx0 : x0 ≫ pullback.snd c g = Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))) :=
    pullback.lift_snd _ _ _

  obtain ⟨s, hs1, hs2⟩ :=
    AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing (pullback.snd c g) x0 hx0
  refine ⟨s ≫ pullback.fst c g, ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]
  · rw [← Category.assoc, hs2, pullback.lift_fst]
  · have hσ : (s ≫ pullback.fst c g) ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]
    intro r g'
    rw [map_mul, AlgebraicGeometry.HenselValue.stalkClosedPointTo_germ_appTop c _ hσ r]

end S_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing (solution)
