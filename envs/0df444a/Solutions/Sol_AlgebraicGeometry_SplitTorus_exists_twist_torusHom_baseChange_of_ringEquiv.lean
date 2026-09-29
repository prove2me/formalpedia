-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.exists_twist_torusHom_baseChange_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0451d3d0-a0e9-5fc1-937b-fbb09952dab1

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

theorem solution
    {R₀ : Type u} [CommRing R₀] {κ : Type u} [Field κ]
    (r : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R₀))
    (sbar : κ ≃+* κ) (hs : Spec.map (CommRingCat.ofHom sbar.toRingHom) ≫ r = r)
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g) (t : ℕ)
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g)) :
    ∃ (Tw : pullback g r ≅ pullback g r) (τ' : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g)),

      Tw.hom ≫ pullback.fst g r = pullback.fst g r ∧
      Tw.hom ≫ pullback.snd g r = pullback.snd g r ≫ Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ∧

      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom)) ≫ τ.1 ≫ Tw.hom ∧

      ((∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
          NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
            (L.baseChange r).mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
              (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ)) →
        ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
          NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ' =
            (L.baseChange r).mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ')
              (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ')) ∧

      (IsClosedImmersion τ.1 → IsClosedImmersion τ'.1) := by
  classical

  let σp : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom sbar.toRingHom)
  let σm : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom sbar.symm.toRingHom)
  have hpm : σp ≫ σm = 𝟙 _ := by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id,
      Spec.map_id]
  have hmp : σm ≫ σp = 𝟙 _ := by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id,
      Spec.map_id]
  have hsp : σp ≫ r = r := hs
  have hsm : σm ≫ r = r := by
    calc σm ≫ r = σm ≫ σp ≫ r := by rw [hsp]
      _ = r := by rw [← Category.assoc, hmp, Category.id_comp]
  haveI : IsIso σm := ⟨⟨σp, hmp, hpm⟩⟩

  let Twh : pullback g r ⟶ pullback g r :=
    pullback.map g r g r (𝟙 G) σm (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hsm])
  haveI : IsIso Twh := inferInstance
  let Tw : pullback g r ≅ pullback g r := asIso Twh
  have hTw1 : Tw.hom ≫ pullback.fst g r = pullback.fst g r := by
    simp only [Tw, Twh, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  have hTw2 : Tw.hom ≫ pullback.snd g r = pullback.snd g r ≫ σm := by
    simp only [Tw, Twh, asIso_hom, pullback.map, pullback.lift_snd]

  let mσ : torusScheme κ t ⟶ torusScheme κ t :=
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom))
  have hmσ : mσ ≫ torusStr κ t = torusStr κ t ≫ σp := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AddMonoidAlgebra.mapRingHom_single]
  let τ' : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g) := ⟨mσ ≫ τ.1 ≫ Tw.hom, by
    change (mσ ≫ τ.1 ≫ Tw.hom) ≫ pullback.snd g r = torusStr κ t
    have h2 : τ.1 ≫ pullback.snd g r = torusStr κ t := τ.2
    rw [Category.assoc, Category.assoc, hTw2, ← Category.assoc τ.1, h2, ← Category.assoc, hmσ, Category.assoc, hpm,
      Category.comp_id]⟩
  refine ⟨Tw, τ', hTw1, hTw2, rfl, ?_, ?_⟩
  ·
    intro hτmul

    have htwist_over : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (RelativeGroupLaw.baseChangeStr r g),
        (σp ≫ x.1 ≫ Tw.hom) ≫ RelativeGroupLaw.baseChangeStr r g = 𝟙 _ := by
      intro x
      change (σp ≫ x.1 ≫ Tw.hom) ≫ pullback.snd g r = 𝟙 _
      have hx : x.1 ≫ pullback.snd g r = 𝟙 _ := x.2
      rw [Category.assoc, Category.assoc, hTw2, ← Category.assoc x.1, hx, Category.id_comp, hpm]
    let twist : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (RelativeGroupLaw.baseChangeStr r g) →
        SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (RelativeGroupLaw.baseChangeStr r g) :=
      fun x => ⟨σp ≫ x.1 ≫ Tw.hom, htwist_over x⟩
    have twist_coe : ∀ x, (twist x).1 = σp ≫ x.1 ≫ Tw.hom := fun x => rfl

    have hψ : σp ≫ (𝟙 (Spec (CommRingCat.of κ)) ≫ r) = 𝟙 (Spec (CommRingCat.of κ)) ≫ r := by
      rw [Category.id_comp, hsp]
    have htoBase : ∀ x, RelativeGroupLaw.baseChangePointToBase r (twist x) =
        GoodReductionJacobian.schemeHomOverComp σp hψ (RelativeGroupLaw.baseChangePointToBase r x) := by
      intro x
      apply Subtype.ext
      rw [RelativeGroupLaw.baseChangePointToBase_coe, GoodReductionJacobian.schemeHomOverComp_coe,
        RelativeGroupLaw.baseChangePointToBase_coe, twist_coe, Category.assoc, Category.assoc, hTw1]
    have twist_mul : ∀ x y, twist ((L.baseChange r).mul _ x y) = (L.baseChange r).mul _ (twist x) (twist y) := by
      intro x y
      have hinj : Function.Injective (RelativeGroupLaw.baseChangePointToBase (f := g) r
          (t' := 𝟙 (Spec (CommRingCat.of κ)))) := fun a b hab => by
        rw [← RelativeGroupLaw.baseChangePointOfBase_toBase r a, hab, RelativeGroupLaw.baseChangePointOfBase_toBase]
      apply hinj
      rw [htoBase, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_mul,
        L.mul_natural _ _ σp hψ, htoBase, htoBase]

    let cs : (torusCoord κ t →ₐ[κ] κ) → (torusCoord κ t →ₐ[κ] κ) := fun η =>
      { toRingHom := sbar.symm.toRingHom.comp (η.toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom))
        commutes' := fun c => by
          simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
            RingHom.comp_apply, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
            RingHom.id_apply, AddMonoidAlgebra.mapRingHom_single]
          change sbar.symm (η (algebraMap κ (torusCoord κ t) (sbar c))) = c
          rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, RingEquiv.symm_apply_apply] }
    have cs_single : ∀ η v, cs η (AddMonoidAlgebra.single v 1) = sbar.symm (η (AddMonoidAlgebra.single v 1)) := by
      intro η v
      change sbar.symm (η (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom (AddMonoidAlgebra.single v 1))) = _
      rw [AddMonoidAlgebra.mapRingHom_single, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_one]

    have hK : ∀ η, NeronModelInfra.schemeHomOverComp (torusPtId κ t η) τ' =
        twist (NeronModelInfra.schemeHomOverComp (torusPtId κ t (cs η)) τ) := by
      intro η
      apply Subtype.ext
      rw [NeronModelInfra.schemeHomOverComp_coe, twist_coe, NeronModelInfra.schemeHomOverComp_coe]
      change Spec.map (CommRingCat.ofHom η.toRingHom) ≫ mσ ≫ τ.1 ≫ Tw.hom =
        σp ≫ (Spec.map (CommRingCat.ofHom (cs η).toRingHom) ≫ τ.1) ≫ Tw.hom
      simp only [← Category.assoc]
      congr 2
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun a => ?_
      change η (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom a) =
        sbar (sbar.symm (η (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom a)))
      rw [RingEquiv.apply_symm_apply]

    have conv_single : ∀ (c c' : WithConv (torusCoord κ t →ₐ[κ] κ)) (v : Fin t → ℤ),
        (c * c') (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
      intro c c' v
      rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul]
      simp
    have hC : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
        cs (χ * χ').ofConv = (WithConv.toConv (cs χ.ofConv) * WithConv.toConv (cs χ'.ofConv)).ofConv := by
      intro χ χ'
      refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
      rw [cs_single]
      change sbar.symm ((χ * χ') (AddMonoidAlgebra.single v 1)) =
        (WithConv.toConv (cs χ.ofConv) * WithConv.toConv (cs χ'.ofConv)) (AddMonoidAlgebra.single v 1)
      rw [conv_single, conv_single, map_mul]
      change _ = cs χ.ofConv (AddMonoidAlgebra.single v 1) * cs χ'.ofConv (AddMonoidAlgebra.single v 1)
      rw [cs_single, cs_single]

    intro χ χ'
    rw [hK, hK, hK, hC, hτmul, twist_mul]
  ·
    intro hci
    change IsClosedImmersion (mσ ≫ τ.1 ≫ Tw.hom)
    haveI := hci
    haveI : IsIso mσ := by
      refine ⟨⟨Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.symm.toRingHom)), ?_, ?_⟩⟩
      · change Spec.map _ ≫ Spec.map _ = 𝟙 _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AddMonoidAlgebra.mapRingHom_comp,
          RingEquiv.toRingHom_comp_symm_toRingHom, AddMonoidAlgebra.mapRingHom_id, CommRingCat.ofHom_id, Spec.map_id]
      · change Spec.map _ ≫ Spec.map _ = 𝟙 _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AddMonoidAlgebra.mapRingHom_comp,
          RingEquiv.symm_toRingHom_comp_toRingHom, AddMonoidAlgebra.mapRingHom_id, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance

end S_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv (solution)
