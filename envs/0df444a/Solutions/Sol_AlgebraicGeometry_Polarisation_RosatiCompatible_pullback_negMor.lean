-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.RosatiCompatible.pullback_negMor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/35d54ae8-3cb5-58d5-a3ca-b943d4ff29ec

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_negMor

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace CF6bBody

variable {S : Type} [CommRing S] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

theorem schemeHomOverComp_inv {T T' : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  letI : Group (SchemeHomOver t' f) := L.pointGroup t'
  let Φ : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (fun x => schemeHomOverComp ψ hψ x) (fun x y => L.mul_natural t t' ψ hψ x y)
  exact map_inv Φ x

theorem schemeHomOverComp_idPt (g : A ⟶ A) (hg : g ≫ f = f) :
    schemeHomOverComp g hg (idPt f) = ⟨g, hg⟩ := by
  apply Subtype.ext; simp [schemeHomOverComp, idPt]

theorem comp_negMor {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    x.1 ≫ negMor f L = (L.inv t x).1 := by
  have h := schemeHomOverComp_inv f L f t x.1 x.2 (idPt f)
  have h2 : schemeHomOverComp x.1 x.2 (idPt f) = x := by apply Subtype.ext; simp [schemeHomOverComp, idPt]
  rw [h2] at h
  have := congrArg Subtype.val h
  simpa [schemeHomOverComp, negMor] using this

theorem act_comp_negMor {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act_hom : ∀ (x : I) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (b : I) : negMor f L ≫ act b = act b ≫ negMor f L := by
  letI : Group (SchemeHomOver f f) := L.pointGroup f
  let Φ : SchemeHomOver f f →* SchemeHomOver f f :=
    MonoidHom.mk' (fun P => pushPt (act b) (act_over b) P) (fun P Q => act_hom b f P Q)
  have h1 : pushPt (act b) (act_over b) (L.inv f (idPt f)) = L.inv f (pushPt (act b) (act_over b) (idPt f)) := map_inv Φ (idPt f)
  have h2 : (pushPt (act b) (act_over b) (idPt f) : SchemeHomOver f f) = ⟨act b, act_over b⟩ := by
    apply Subtype.ext; simp [idPt]
  rw [h2] at h1
  have := congrArg Subtype.val h1
  rw [mapPt_coe] at this

  change (L.inv f (idPt f)).1 ≫ act b = act b ≫ negMor f L
  rw [this, ← comp_negMor f L f ⟨act b, act_over b⟩]

theorem locIsoOnBase_of_iso {S' : Type} [CommRing S'] {X : Scheme} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

end CF6bBody

open CF6bBody in
theorem solution
    {S : Type} [CommRing S] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act_hom : ∀ (x : I) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (star : I → I) (𝓛 : A.Modules) (h : Scheme.Modules.IsInvertible 𝓛)
    (hR : RosatiCompatible f L 𝓛 act act_over star) :
    RosatiCompatible f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) act act_over star := by
  intro b
  have hNf : negMor f L ≫ f = f := negMor_over f L
  let NN : pullback f f ⟶ pullback f f :=
    pullback.lift ((pullback.fst f f) ≫ negMor f L) ((pullback.snd f f) ≫ negMor f L) (by simp only [Category.assoc, hNf]; exact pullback.condition)
  have hNN1 : NN ≫ (pullback.fst f f) = (pullback.fst f f) ≫ negMor f L := pullback.lift_fst _ _ _
  have hNN2 : NN ≫ (pullback.snd f f) = (pullback.snd f f) ≫ negMor f L := pullback.lift_snd _ _ _
  have hNNt : NN ≫ (pullback.fst f f ≫ f) = (pullback.fst f f ≫ f) := by
    rw [← Category.assoc, hNN1, Category.assoc, hNf]

  have hmN : addMor f L ≫ negMor f L = NN ≫ addMor f L := by
    letI : Group (SchemeHomOver (pullback.fst f f ≫ f) f) := L.pointGroup (pullback.fst f f ≫ f)
    let P₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨(pullback.fst f f), rfl⟩
    let P₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨(pullback.snd f f), pullback.condition.symm⟩
    have e₁ : schemeHomOverComp NN hNNt P₁ = L.inv (pullback.fst f f ≫ f) P₁ := by
      apply Subtype.ext
      show NN ≫ (pullback.fst f f) = (L.inv (pullback.fst f f ≫ f) P₁).1
      rw [hNN1]; exact comp_negMor f L (pullback.fst f f ≫ f) P₁
    have e₂ : schemeHomOverComp NN hNNt P₂ = L.inv (pullback.fst f f ≫ f) P₂ := by
      apply Subtype.ext
      show NN ≫ (pullback.snd f f) = (L.inv (pullback.fst f f ≫ f) P₂).1
      rw [hNN2]; exact comp_negMor f L (pullback.fst f f ≫ f) P₂
    have lhs : addMor f L ≫ negMor f L = (L.inv (pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f) P₁ P₂)).1 := comp_negMor f L (pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f) P₁ P₂)
    have rhs : NN ≫ addMor f L = (L.mul (pullback.fst f f ≫ f) (L.inv (pullback.fst f f ≫ f) P₁) (L.inv (pullback.fst f f ≫ f) P₂)).1 := by
      have := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) NN hNNt P₁ P₂)
      rw [e₁, e₂] at this
      simp [schemeHomOverComp] at this ⊢
      exact this
    rw [lhs, rhs]
    congr 1
    show (P₁ * P₂)⁻¹ = P₁⁻¹ * P₂⁻¹
    rw [mul_inv_rev]; exact hc.mul_comm (pullback.fst f f ≫ f) _ _

  have hNact : ∀ c : I, negMor f L ≫ act c = act c ≫ negMor f L := fun c => act_comp_negMor f L act act_over act_hom c

  obtain ⟨ed⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (negMor f L) h
  have pullAlong : ∀ (q : pullback f f ⟶ A) (hq : NN ≫ q = q ≫ negMor f L) (M : A.Modules),
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (negMor f L)).obj M) ≅
        (Scheme.Modules.pullback NN).obj ((Scheme.Modules.pullback q).obj M) := fun q hq M =>
    (Scheme.Modules.pullbackComp q (negMor f L)).app M ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp NN q).app M).symm
  let eΛ : mumfordBundle f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) ≅
      (Scheme.Modules.pullback NN).obj (mumfordBundle f L 𝓛) :=
    ((pullAlong (addMor f L) hmN.symm 𝓛) ⊗ᵢ
      (((Scheme.Modules.pullback (pullback.fst f f)).mapIso ed.symm ≪≫ pullAlong (pullback.fst f f) hNN1 (Scheme.Modules.dual 𝓛)) ⊗ᵢ
       ((Scheme.Modules.pullback (pullback.snd f f)).mapIso ed.symm ≪≫ pullAlong (pullback.snd f f) hNN2 (Scheme.Modules.dual 𝓛)))) ≪≫
    (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso NN _ _).symm) ≪≫
    (Scheme.Modules.pullbackTensorObjIso NN _ _).symm

  have along : ∀ (r : pullback f f ⟶ pullback f f) (hr : r ≫ NN = NN ≫ r),
      Nonempty ((Scheme.Modules.pullback r).obj (mumfordBundle f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛)) ≅
        (Scheme.Modules.pullback NN).obj ((Scheme.Modules.pullback r).obj (mumfordBundle f L 𝓛))) := fun r hr =>
    ⟨(Scheme.Modules.pullback r).mapIso eΛ ≪≫ (Scheme.Modules.pullbackComp r NN).app _ ≪≫
      (Scheme.Modules.pullbackCongr hr).app _ ≪≫ ((Scheme.Modules.pullbackComp NN r).app _).symm⟩

  have hr : pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition) ≫ NN =
      NN ≫ pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition) := by
    apply pullback.hom_ext
    · have l1 : (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition) ≫ NN) ≫ pullback.fst f f = pullback.fst f f ≫ negMor f L := by
        rw [Category.assoc, hNN1, ← Category.assoc, pullback.lift_fst]
      have l2 : (NN ≫ pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.fst f f = pullback.fst f f ≫ negMor f L := by
        rw [Category.assoc, pullback.lift_fst, hNN1]
      exact l1.trans l2.symm
    · have l1 : (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition) ≫ NN) ≫ pullback.snd f f = pullback.snd f f ≫ act b ≫ negMor f L := by
        rw [Category.assoc, hNN2, ← Category.assoc, pullback.lift_snd, Category.assoc]
      have l2 : (NN ≫ pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.snd f f = pullback.snd f f ≫ act b ≫ negMor f L := by
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hNN2, Category.assoc, hNact]
      exact l1.trans l2.symm
  have hl : pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition) ≫ NN =
      NN ≫ pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition) := by
    apply pullback.hom_ext
    · have l1 : (pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition) ≫ NN) ≫ pullback.fst f f = pullback.fst f f ≫ act (star b) ≫ negMor f L := by
        rw [Category.assoc, hNN1, ← Category.assoc, pullback.lift_fst, Category.assoc]
      have l2 : (NN ≫ pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.fst f f = pullback.fst f f ≫ act (star b) ≫ negMor f L := by
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hNN1, Category.assoc, hNact]
      exact l1.trans l2.symm
    · have l1 : (pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition) ≫ NN) ≫ pullback.snd f f = pullback.snd f f ≫ negMor f L := by
        rw [Category.assoc, hNN2, ← Category.assoc, pullback.lift_snd]
      have l2 : (NN ≫ pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.snd f f = pullback.snd f f ≫ negMor f L := by
        rw [Category.assoc, pullback.lift_snd, hNN2]
      exact l1.trans l2.symm
  obtain ⟨er⟩ := along _ hr
  obtain ⟨el⟩ := along _ hl

  have key := LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) NN (𝟙 _) (by rw [Category.comp_id]; exact hNNt) (hR b)
  have E := LocIsoOnBase.equivalence (pullback.fst f f ≫ f)
  exact E.trans (E.trans (locIsoOnBase_of_iso _ er) key) (locIsoOnBase_of_iso _ el.symm)

end S_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_negMor
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_pullback_negMor (solution)
