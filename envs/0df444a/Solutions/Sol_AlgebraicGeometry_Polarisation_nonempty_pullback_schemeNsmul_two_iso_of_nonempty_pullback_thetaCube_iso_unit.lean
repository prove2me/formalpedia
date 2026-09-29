-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e44b7e6c-3ff8-5752-996c-77e5eb124d1e

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard"

namespace ThetaDiag

variable {R : Type} [CommRing R] {B : Scheme} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)

theorem mul_val_congr' {T : Scheme} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂)
    (P Q : SchemeHomOver t₁ g) (P' Q' : SchemeHomOver t₂ g) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (G.mul t₁ P Q).1 = (G.mul t₂ P' Q').1 := by
  subst ht; cases Subtype.ext hP; cases Subtype.ext hQ; rfl

theorem one_val_congr {T : Scheme} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂) :
    (G.one t₁).1 = (G.one t₂).1 := by
  subst ht; rfl

theorem comp_addMor {T : Scheme} (ρ : T ⟶ pullback g g) {t : T ⟶ Spec (CommRingCat.of R)}
    (ht : ρ ≫ pullback.fst g g ≫ g = t) (P Q : SchemeHomOver t g)
    (hP : ρ ≫ pullback.fst g g = P.1) (hQ : ρ ≫ pullback.snd g g = Q.1) :
    ρ ≫ addMor g G = (G.mul t P Q).1 := by
  have h := G.mul_natural (pullback.fst g g ≫ g) (ρ ≫ pullback.fst g g ≫ g) ρ rfl
    ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩
  have h1 := congrArg Subtype.val h
  refine h1.trans ?_
  exact mul_val_congr' G ht _ _ _ _ hP hQ

theorem diag_comp_addMor :
    pullback.lift (𝟙 B) (𝟙 B) rfl ≫ addMor g G = G.schemeNsmul 2 := by
  have e : G.schemeNsmul 2 = (G.mul g RelativeGroupLaw.idPoint RelativeGroupLaw.idPoint).1 := by
    show (G.nsmul g 2 RelativeGroupLaw.idPoint).1 = _
    rw [G.nsmul_succ, G.nsmul_one_apply]
  rw [e]
  exact comp_addMor G _ (by rw [pullback.lift_fst_assoc, Category.id_comp]) _ _
    (by rw [pullback.lift_fst]; try rfl) (by rw [pullback.lift_snd]; try rfl)

theorem two_neg_comp_addMor :
    pullback.lift (G.schemeNsmul 2) (negMor g G) (by rw [G.schemeNsmul_over, negMor_over]) ≫ addMor g G = 𝟙 B := by
  letI := G.pointGroup g
  have key : (G.mul g (G.nsmul g 2 RelativeGroupLaw.idPoint) (G.inv g (idPt g))).1 = 𝟙 B := by
    have hid : (RelativeGroupLaw.idPoint : SchemeHomOver g g) = idPt g := rfl
    rw [G.nsmul_succ, G.nsmul_one_apply, hid]
    have : (idPt g * idPt g) * (idPt g)⁻¹ = idPt g := mul_inv_cancel_right _ _
    exact congrArg Subtype.val this
  rw [← key]
  exact comp_addMor G _ (by rw [pullback.lift_fst_assoc, G.schemeNsmul_over]) _ _
    (by rw [pullback.lift_fst]; try rfl) (by rw [pullback.lift_snd]; try rfl)

theorem id_neg_comp_addMor :
    pullback.lift (𝟙 B) (negMor g G) (by rw [Category.id_comp, negMor_over]) ≫ addMor g G = (G.one g).1 := by
  letI := G.pointGroup g
  have key : (G.mul g (idPt g) (G.inv g (idPt g))).1 = (G.one g).1 := by
    have : idPt g * (idPt g)⁻¹ = 1 := mul_inv_cancel _
    exact congrArg Subtype.val this
  rw [← key]
  exact comp_addMor G _ (by rw [pullback.lift_fst_assoc, Category.id_comp]) _ _
    (by rw [pullback.lift_fst]; try rfl) (by rw [pullback.lift_snd]; try rfl)

theorem one_val_eq_comp :
    (G.one g).1 = g ≫ (G.one (𝟙 _)).1 := by
  have h := G.one_natural (𝟙 _) g g (Category.comp_id g)
  exact (congrArg Subtype.val h).symm

end ThetaDiag

namespace ThetaDiag

section Skel

variable {X Y Z : Scheme}

theorem sk_congr {P Q : X.Modules} (e : P ≅ Q) : toSkeleton P = toSkeleton Q := congr_toSkeleton_of_iso e

theorem sk_tensor (P Q : X.Modules) : toSkeleton (P ⊗ Q) = toSkeleton P * toSkeleton Q :=
  Skeleton.toSkeleton_tensorObj P Q

theorem sk_unit : toSkeleton (𝟙_ X.Modules) = 1 := rfl

theorem sk_pullback_tensor (ρ : Y ⟶ X) (P Q : X.Modules) :
    toSkeleton ((Scheme.Modules.pullback ρ).obj (P ⊗ Q)) =
      toSkeleton ((Scheme.Modules.pullback ρ).obj P) * toSkeleton ((Scheme.Modules.pullback ρ).obj Q) :=
  (sk_congr (Scheme.Modules.pullbackTensorObjIso ρ P Q)).trans (sk_tensor _ _)

theorem sk_pullback_dual (ρ : Y ⟶ X) {P : X.Modules} (hP : Scheme.Modules.IsInvertible P) :
    toSkeleton ((Scheme.Modules.pullback ρ).obj (Scheme.Modules.dual P)) =
      toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback ρ).obj P)) :=
  sk_congr (hP.pullback_dual_monoidalV2 ρ).some

theorem sk_dual_mul {P : X.Modules} (hP : Scheme.Modules.IsInvertible P) :
    toSkeleton (Scheme.Modules.dual P) * toSkeleton P = 1 := by
  rw [mul_comm, ← sk_tensor]
  exact sk_congr (hP.dual_monoidalV2).2.some

theorem sk_dual_congr {P Q : X.Modules} (hP : Scheme.Modules.IsInvertible P) (hQ : Scheme.Modules.IsInvertible Q)
    (h : toSkeleton P = toSkeleton Q) :
    toSkeleton (Scheme.Modules.dual P) = toSkeleton (Scheme.Modules.dual Q) := by
  have h1 := sk_dual_mul hP
  have h2 := sk_dual_mul hQ
  rw [← h] at h2
  calc toSkeleton (Scheme.Modules.dual P)
      = toSkeleton (Scheme.Modules.dual P) * (toSkeleton (Scheme.Modules.dual Q) * toSkeleton P) := by rw [h2, mul_one]
    _ = toSkeleton (Scheme.Modules.dual Q) * (toSkeleton (Scheme.Modules.dual P) * toSkeleton P) := by
        rw [mul_left_comm]
    _ = toSkeleton (Scheme.Modules.dual Q) := by rw [h1, mul_one]

theorem sk_pullback_comp (ρ : Z ⟶ Y) (σ : Y ⟶ X) (P : X.Modules) :
    toSkeleton ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback σ).obj P)) =
      toSkeleton ((Scheme.Modules.pullback (ρ ≫ σ)).obj P) :=
  sk_congr ((Scheme.Modules.pullbackComp ρ σ).app P)

theorem sk_pullback_congr {ρ ρ' : Y ⟶ X} (h : ρ = ρ') (P : X.Modules) :
    toSkeleton ((Scheme.Modules.pullback ρ).obj P) = toSkeleton ((Scheme.Modules.pullback ρ').obj P) :=
  sk_congr ((Scheme.Modules.pullbackCongr h).app P)

theorem sk_pullback_id (P : X.Modules) : toSkeleton ((Scheme.Modules.pullback (𝟙 X)).obj P) = toSkeleton P :=
  sk_congr ((Scheme.Modules.pullbackId X).app P)

theorem sk_pullback_unit (ρ : Y ⟶ X) : toSkeleton ((Scheme.Modules.pullback ρ).obj (𝟙_ X.Modules)) = 1 :=
  sk_congr (Scheme.Modules.pullbackUnitIso ρ)

theorem sk_pullback_obj_congr (ρ : Y ⟶ X) {P Q : X.Modules} (h : toSkeleton P = toSkeleton Q) :
    toSkeleton ((Scheme.Modules.pullback ρ).obj P) = toSkeleton ((Scheme.Modules.pullback ρ).obj Q) :=
  sk_congr ((Scheme.Modules.pullback ρ).mapIso (Skeleton.isoOfEq h))

theorem isInvertible_dual {P : X.Modules} (hP : Scheme.Modules.IsInvertible P) :
    Scheme.Modules.IsInvertible (Scheme.Modules.dual P) := (hP.dual_monoidalV2).1

end Skel

variable {R : Type} [CommRing R] {B : Scheme} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)

theorem isInvertible_mumfordBundle {N : B.Modules} (hN : Scheme.Modules.IsInvertible N) :
    Scheme.Modules.IsInvertible (mumfordBundle g G N) :=
  (hN.pullback _).tensor_monoidalV2 (((isInvertible_dual hN).pullback _).tensor_monoidalV2 ((isInvertible_dual hN).pullback _))

theorem sk_pullback_mumfordBundle {T : Scheme} (ρ : T ⟶ pullback g g) {N : B.Modules} (hN : Scheme.Modules.IsInvertible N) :
    toSkeleton ((Scheme.Modules.pullback ρ).obj (mumfordBundle g G N)) =
      toSkeleton ((Scheme.Modules.pullback (ρ ≫ addMor g G)).obj N) *
        (toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback (ρ ≫ pullback.fst g g)).obj N)) *
         toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback (ρ ≫ pullback.snd g g)).obj N))) := by
  unfold mumfordBundle
  rw [sk_pullback_tensor, sk_pullback_tensor, sk_pullback_comp, sk_pullback_comp ρ (pullback.fst g g),
    sk_pullback_comp ρ (pullback.snd g g), sk_pullback_dual _ hN, sk_pullback_dual _ hN]

end ThetaDiag

namespace ThetaDiag

theorem baseChange_one_val_eq_rigSection
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    ((L.baseChange ι).one (𝟙 (Spec (CommRingCat.of R)))).1 = rigSection f ι (L.one (𝟙 (Spec (CommRingCat.of S)))) := by
  apply pullback.hom_ext
  · have h1 : ((L.baseChange ι).one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ pullback.fst f ι =
        (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).one (𝟙 (Spec (CommRingCat.of R))))).1 := rfl
    rw [h1, show (L.baseChange ι).one (𝟙 _) = RelativeGroupLaw.baseChangePointOfBase ι (L.one (𝟙 _ ≫ ι)) from rfl,
      RelativeGroupLaw.baseChangePointToBase_ofBase]
    unfold rigSection
    rw [pullback.lift_fst, one_val_congr L (show 𝟙 _ ≫ ι = ι ≫ 𝟙 _ by simp)]
    exact (congrArg Subtype.val (L.one_natural (𝟙 _) (ι ≫ 𝟙 _) ι rfl)).symm
  · unfold rigSection
    rw [pullback.lift_snd]
    exact ((L.baseChange ι).one (𝟙 (Spec (CommRingCat.of R)))).2

end ThetaDiag

open ThetaDiag in
theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
    (h : Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι))
          (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over]))).obj
        ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)))) ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅
      (N.L ⊗ N.L ⊗ N.L) ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L)  := by
  classical
  obtain ⟨eΘ⟩ := h
  have hN := N.isInvertible
  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) := isInvertible_mumfordBundle (L.baseChange ι) hN

  have hdμ : (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over])) ≫ (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι)) (by rw [Category.assoc, addMor_over]; exact pullback.condition)) = (pullback.lift ((L.baseChange ι).schemeNsmul 2) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [(L.baseChange ι).schemeNsmul_over, negMor_over])) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, diag_comp_addMor, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  have hd13 : (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over])) ≫ (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι)) (by rw [Category.assoc]; exact pullback.condition)) = (pullback.lift (𝟙 _) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [Category.id_comp, negMor_over])) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  have hd23 : (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over])) ≫ (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι)) (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition)) = (pullback.lift (𝟙 _) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [Category.id_comp, negMor_over])) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

  have hs : toSkeleton ((Scheme.Modules.pullback (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over]))).obj
        ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L))))) = 1 := sk_congr eΘ

  set u := toSkeleton N.L with hu
  set q := toSkeleton ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L) with hq
  set v := toSkeleton ((Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) with hv
  set u' := toSkeleton (Scheme.Modules.dual N.L) with hu'
  set q' := toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L)) with hq'
  set v' := toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L)) with hv'
  set w := toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [Category.id_comp, negMor_over]))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L))) with hw
  have huu : u' * u = 1 := sk_dual_mul hN
  have hqq : q' * q = 1 := sk_dual_mul (hN.pullback _)
  have hvv : v' * v = 1 := sk_dual_mul (hN.pullback _)

  have eτ : toSkeleton ((Scheme.Modules.pullback (pullback.lift ((L.baseChange ι).schemeNsmul 2) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [(L.baseChange ι).schemeNsmul_over, negMor_over]))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) = u * (q' * v') := by
    rw [sk_pullback_mumfordBundle (L.baseChange ι) _ hN, sk_pullback_congr (two_neg_comp_addMor (L.baseChange ι)), sk_pullback_id,
      sk_dual_congr (hN.pullback _) (hN.pullback _) (sk_pullback_congr (pullback.lift_fst _ _ _) N.L),
      sk_dual_congr (hN.pullback _) (hN.pullback _) (sk_pullback_congr (pullback.lift_snd _ _ _) N.L)]

  have he₀ : toSkeleton ((Scheme.Modules.pullback (((L.baseChange ι).one (𝟙 _)).1)).obj N.L) = toSkeleton (𝟙_ _) := by
    rw [sk_pullback_congr (baseChange_one_val_eq_rigSection L R ι) N.L]
    exact sk_congr N.rigidified.some
  have eσ : toSkeleton ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [Category.id_comp, negMor_over]))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) = u' * v' := by
    rw [sk_pullback_mumfordBundle (L.baseChange ι) _ hN, sk_pullback_congr (id_neg_comp_addMor (L.baseChange ι)),
      sk_pullback_congr (one_val_eq_comp (L.baseChange ι)), ← sk_pullback_comp, sk_pullback_obj_congr _ he₀, sk_pullback_unit, one_mul,
      sk_dual_congr (hN.pullback _) hN ((sk_pullback_congr (pullback.lift_fst _ _ _) N.L).trans (sk_pullback_id N.L)),
      sk_dual_congr (hN.pullback _) (hN.pullback _) (sk_pullback_congr (pullback.lift_snd _ _ _) N.L)]
  have hww : w * (u' * v') = 1 := by rw [← eσ]; exact sk_dual_mul (hΛ.pullback _)

  have eΘ' : toSkeleton ((Scheme.Modules.pullback (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι)) (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over]))).obj
        ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L))))) = u * (q' * v') * (w * w) := by
    rw [sk_pullback_tensor, sk_pullback_tensor, sk_pullback_comp _ (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι)) (by rw [Category.assoc, addMor_over]; exact pullback.condition)), sk_pullback_congr hdμ, eτ,
      sk_pullback_dual _ (hΛ.pullback _), sk_pullback_dual _ (hΛ.pullback _),
      sk_dual_congr ((hΛ.pullback _).pullback _) (hΛ.pullback _)
        ((sk_pullback_comp _ (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι)) (by rw [Category.assoc]; exact pullback.condition)) _).trans (sk_pullback_congr hd13 _)),
      sk_dual_congr ((hΛ.pullback _).pullback _) (hΛ.pullback _)
        ((sk_pullback_comp _ (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι)) (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition)) _).trans (sk_pullback_congr hd23 _))]
  rw [eΘ'] at hs

  have hw1 : w = u * v := by
    have e1 : w * (u' * u) * (v' * v) = (w * (u' * v')) * (u * v) := by ac_rfl
    rw [huu, hvv, mul_one, mul_one, hww, one_mul] at e1
    exact e1
  rw [hw1] at hs
  have e2 : q * (u * (q' * v') * (u * v * (u * v))) = (q' * q) * (v' * v) * (u * (u * u) * v) := by ac_rfl
  rw [hs, mul_one, hqq, hvv, one_mul, one_mul] at e2
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [sk_tensor, sk_tensor, sk_tensor]
  exact e2

end S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit (solution)
