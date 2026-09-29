-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/72b7735d-7212-5436-af01-4f416b5d1a79

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesRigidifyV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard"

noncomputable section

namespace W1a

open AlgebraicGeometry.Scheme.Modules

section modules

variable {X Y Z : Scheme.{0}}

theorem isInvertible_tensorUnit (X : Scheme.{0}) : IsInvertible (𝟙_ X.Modules) := by
  rw [Scheme.Modules.tensorUnit_eq]; exact isInvertible_unit X

def dualUnitIso (X : Scheme.{0}) : Scheme.Modules.dual (𝟙_ X.Modules) ≅ 𝟙_ X.Modules :=
  (λ_ _).symm ≪≫ (IsInvertible.dual_monoidalV2 (isInvertible_tensorUnit X)).2.some

def tensorDualIso {W : X.Modules} (hW : IsInvertible W) : W ⊗ Scheme.Modules.dual W ≅ 𝟙_ _ :=
  (IsInvertible.dual_monoidalV2 hW).2.some

theorem isInvertible_dual {W : X.Modules} (hW : IsInvertible W) : IsInvertible (Scheme.Modules.dual W) :=
  (IsInvertible.dual_monoidalV2 hW).1

def tensor_dual_dual_iso_left {W A : X.Modules} (hW : IsInvertible W) (e : A ≅ 𝟙_ _) :
    W ⊗ (Scheme.Modules.dual A ⊗ Scheme.Modules.dual W) ≅ 𝟙_ _ :=
  whiskerLeftIso W (whiskerRightIso (dualMapIso e ≪≫ dualUnitIso X) _ ≪≫ λ_ _) ≪≫ tensorDualIso hW

def tensor_dual_dual_iso_right {W A : X.Modules} (hW : IsInvertible W) (e : A ≅ 𝟙_ _) :
    W ⊗ (Scheme.Modules.dual W ⊗ Scheme.Modules.dual A) ≅ 𝟙_ _ :=
  whiskerLeftIso W (whiskerLeftIso _ (dualMapIso e ≪≫ dualUnitIso X) ≪≫ ρ_ _) ≪≫ tensorDualIso hW

def triple_iso_unit {A B C : X.Modules} (eA : A ≅ 𝟙_ _) (eB : B ≅ 𝟙_ _) (eC : C ≅ 𝟙_ _) :
    A ⊗ (Scheme.Modules.dual B ⊗ Scheme.Modules.dual C) ≅ 𝟙_ _ :=
  (eA ⊗ᵢ ((dualMapIso eB ≪≫ dualUnitIso X) ⊗ᵢ (dualMapIso eC ≪≫ dualUnitIso X))) ≪≫
    whiskerLeftIso _ (λ_ _) ≪≫ λ_ _

theorem nonempty_pullback_triple_iso (φ : X ⟶ Y) (A : Y.Modules) {B C : Y.Modules} (hB : IsInvertible B) (hC : IsInvertible C) :
    Nonempty ((Scheme.Modules.pullback φ).obj (A ⊗ (Scheme.Modules.dual B ⊗ Scheme.Modules.dual C)) ≅
      (Scheme.Modules.pullback φ).obj A ⊗
        (Scheme.Modules.dual ((Scheme.Modules.pullback φ).obj B) ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback φ).obj C))) := by
  obtain ⟨dB⟩ := hB.pullback_dual_monoidalV2 φ
  obtain ⟨dC⟩ := hC.pullback_dual_monoidalV2 φ
  exact ⟨pullbackTensorObjIso φ _ _ ≪≫ whiskerLeftIso _ (pullbackTensorObjIso φ _ _ ≪≫ (dB ⊗ᵢ dC))⟩

theorem isInvertible_triple {A B C : X.Modules} (hA : IsInvertible A) (hB : IsInvertible B) (hC : IsInvertible C) :
    IsInvertible (A ⊗ (Scheme.Modules.dual B ⊗ Scheme.Modules.dual C)) :=
  hA.tensor_monoidalV2 ((isInvertible_dual hB).tensor_monoidalV2 (isInvertible_dual hC))

def pullbackCompCongr {φ : X ⟶ Y} {ψ : Y ⟶ Z} {χ : X ⟶ Z} (h : φ ≫ ψ = χ) (M : Z.Modules) :
    (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj M) ≅ (Scheme.Modules.pullback χ).obj M :=
  (pullbackComp φ ψ).app M ≪≫ (pullbackCongr h).app M

theorem locIsoOnBase_unit_of_iso {S' : Type} [CommRing S'] (q : X ⟶ Spec (CommRingCat.of S')) {M : X.Modules} (e : M ≅ 𝟙_ _) :
    LocIsoOnBase q M (𝟙_ _) :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

end modules

section law

variable {R : Type} [CommRing R] {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R g)

theorem lift_addMor {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver t g) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ addMor g G = (G.mul t x y).1 := by
  have hψ : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ (pullback.fst g g ≫ g) = t := by
    rw [pullback.lift_fst_assoc]; exact x.2
  have h := G.mul_natural (pullback.fst g g ≫ g) t (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
    ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩
  have hx : schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      (⟨pullback.fst g g, rfl⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) = x :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have hy : schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      (⟨pullback.snd g g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) = y :=
    Subtype.ext (pullback.lift_snd _ _ _)
  rw [hx, hy] at h
  exact congrArg Subtype.val h

theorem one_coe_eq {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : (G.one t).1 = t ≫ (G.one (𝟙 _)).1 :=
  (congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id t))).symm

variable (N₀ : B.Modules) (hN : IsInvertible N₀)
  (hrig : Nonempty ((Scheme.Modules.pullback (G.one (𝟙 (Spec (CommRingCat.of R)))).1).obj N₀ ≅ 𝟙_ _))

include hrig in

theorem nonempty_pullback_one_iso {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Scheme.Modules.pullback (G.one t).1).obj N₀ ≅ 𝟙_ _) :=
  ⟨(pullbackCongr (one_coe_eq G t)).app N₀ ≪≫ (pullbackCompCongr rfl N₀).symm ≪≫
    (Scheme.Modules.pullback t).mapIso hrig.some ≪≫ pullbackTensorUnitObjIso t⟩

include hN in

theorem nonempty_pullback_mumford_pair {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver t g) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift x.1 y.1 (x.2.trans y.2.symm))).obj (mumfordBundle g G N₀) ≅
      (Scheme.Modules.pullback (G.mul t x y).1).obj N₀ ⊗
        (Scheme.Modules.dual ((Scheme.Modules.pullback x.1).obj N₀) ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback y.1).obj N₀))) := by
  obtain ⟨dx⟩ := hN.pullback_dual_monoidalV2 x.1
  obtain ⟨dy⟩ := hN.pullback_dual_monoidalV2 y.1
  refine ⟨pullbackTensorObjIso _ _ _ ≪≫ (pullbackCompCongr (lift_addMor G x y) N₀ ⊗ᵢ (pullbackTensorObjIso _ _ _ ≪≫
    ((pullbackCompCongr (pullback.lift_fst _ _ _) (Scheme.Modules.dual N₀) ≪≫ dx) ⊗ᵢ
     (pullbackCompCongr (pullback.lift_snd _ _ _) (Scheme.Modules.dual N₀) ≪≫ dy))))⟩

include hN in
theorem isInvertible_mumford : IsInvertible (mumfordBundle g G N₀) :=
  (hN.pullback _).tensor_monoidalV2 (((isInvertible_dual hN).pullback _).tensor_monoidalV2 ((isInvertible_dual hN).pullback _))

include hN hrig in

theorem nonempty_mumford_one_left {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t g) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (G.one t).1 y.1 ((G.one t).2.trans y.2.symm))).obj (mumfordBundle g G N₀) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_pullback_mumford_pair G N₀ hN (G.one t) y
  obtain ⟨u⟩ := nonempty_pullback_one_iso G N₀ hrig t
  exact ⟨e ≪≫ ((pullbackCongr (congrArg Subtype.val (G.one_mul t y))).app N₀ ⊗ᵢ Iso.refl _) ≪≫
    tensor_dual_dual_iso_left (hN.pullback y.1) u⟩

include hN hrig in

theorem nonempty_mumford_one_right {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift x.1 (G.one t).1 (x.2.trans (G.one t).2.symm))).obj (mumfordBundle g G N₀) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_pullback_mumford_pair G N₀ hN x (G.one t)
  obtain ⟨u⟩ := nonempty_pullback_one_iso G N₀ hrig t
  exact ⟨e ≪≫ ((pullbackCongr (congrArg Subtype.val (G.mul_one t x))).app N₀ ⊗ᵢ Iso.refl _) ≪≫
    tensor_dual_dual_iso_right (hN.pullback x.1) u⟩

end law

section theta

variable {R : Type} [CommRing R] {B : Scheme.{0}} (g : B ⟶ Spec (CommRingCat.of R)) (G : RelativeGroupLaw R g) (N₀ : B.Modules)

def aMap : pullback (prodStr g g) g ⟶ pullback g g :=
  pullback.lift (pullback.fst (prodStr g g) g ≫ addMor g G) (pullback.snd (prodStr g g) g)
    (by rw [Category.assoc, addMor_over]; exact pullback.condition)

def b1Map : pullback (prodStr g g) g ⟶ pullback g g :=
  pullback.lift (pullback.fst (prodStr g g) g ≫ pullback.fst g g) (pullback.snd (prodStr g g) g)
    (by rw [Category.assoc]; exact pullback.condition)

def b2Map : pullback (prodStr g g) g ⟶ pullback g g :=
  pullback.lift (pullback.fst (prodStr g g) g ≫ pullback.snd g g) (pullback.snd (prodStr g g) g)
    (by rw [Category.assoc, ← pullback.condition (f := g) (g := g)]; exact pullback.condition)

def theta : (pullback (prodStr g g) g).Modules :=
  (Scheme.Modules.pullback (aMap g G)).obj (mumfordBundle g G N₀) ⊗
    (Scheme.Modules.dual ((Scheme.Modules.pullback (b1Map g)).obj (mumfordBundle g G N₀)) ⊗
      Scheme.Modules.dual ((Scheme.Modules.pullback (b2Map g)).obj (mumfordBundle g G N₀)))

@[scoped simp] theorem aMap_fst : aMap g G ≫ pullback.fst g g = pullback.fst (prodStr g g) g ≫ addMor g G := pullback.lift_fst _ _ _
@[scoped simp] theorem aMap_snd : aMap g G ≫ pullback.snd g g = pullback.snd (prodStr g g) g := pullback.lift_snd _ _ _
@[scoped simp] theorem b1Map_fst : b1Map g ≫ pullback.fst g g = pullback.fst (prodStr g g) g ≫ pullback.fst g g := pullback.lift_fst _ _ _
@[scoped simp] theorem b1Map_snd : b1Map g ≫ pullback.snd g g = pullback.snd (prodStr g g) g := pullback.lift_snd _ _ _
@[scoped simp] theorem b2Map_fst : b2Map g ≫ pullback.fst g g = pullback.fst (prodStr g g) g ≫ pullback.snd g g := pullback.lift_fst _ _ _
@[scoped simp] theorem b2Map_snd : b2Map g ≫ pullback.snd g g = pullback.snd (prodStr g g) g := pullback.lift_snd _ _ _

variable (hN : IsInvertible N₀)
  (hrig : Nonempty ((Scheme.Modules.pullback (G.one (𝟙 (Spec (CommRingCat.of R)))).1).obj N₀ ≅ 𝟙_ _))

include hN in
theorem isInvertible_theta : IsInvertible (theta g G N₀) :=
  isInvertible_triple ((isInvertible_mumford G N₀ hN).pullback _) ((isInvertible_mumford G N₀ hN).pullback _)
    ((isInvertible_mumford G N₀ hN).pullback _)

include hN in

theorem nonempty_pullback_theta {T : Scheme.{0}} (φ : T ⟶ pullback (prodStr g g) g) (α β γ : T ⟶ pullback g g)
    (hα : φ ≫ aMap g G = α) (hβ : φ ≫ b1Map g = β) (hγ : φ ≫ b2Map g = γ) :
    Nonempty ((Scheme.Modules.pullback φ).obj (theta g G N₀) ≅
      (Scheme.Modules.pullback α).obj (mumfordBundle g G N₀) ⊗
        (Scheme.Modules.dual ((Scheme.Modules.pullback β).obj (mumfordBundle g G N₀)) ⊗
          Scheme.Modules.dual ((Scheme.Modules.pullback γ).obj (mumfordBundle g G N₀)))) := by
  obtain ⟨e⟩ := nonempty_pullback_triple_iso φ ((Scheme.Modules.pullback (aMap g G)).obj (mumfordBundle g G N₀))
    ((isInvertible_mumford G N₀ hN).pullback (b1Map g)) ((isInvertible_mumford G N₀ hN).pullback (b2Map g))
  exact ⟨e ≪≫ (pullbackCompCongr hα _ ⊗ᵢ (dualMapIso (pullbackCompCongr hβ _) ⊗ᵢ dualMapIso (pullbackCompCongr hγ _)))⟩

theorem prod_one_coe_fst {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ((G.prod G).one t).1 ≫ pullback.fst g g = (G.one t).1 := by
  rw [RelativeGroupLaw.prod_one, prodPairPt_coe, pullback.lift_fst]

theorem prod_one_coe_snd {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ((G.prod G).one t).1 ≫ pullback.snd g g = (G.one t).1 := by
  rw [RelativeGroupLaw.prod_one, prodPairPt_coe, pullback.lift_snd]

theorem rigSection_eq :
    rigSection (prodStr g g) g ((G.prod G).one (𝟙 _)) =
      pullback.lift (pullback.lift (G.one g).1 (G.one g).1 rfl) (𝟙 B)
        (by rw [pullback.lift_fst_assoc, (G.one g).2, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, prod_one_coe_fst, pullback.lift_fst, one_coe_eq G g]
    · rw [Category.assoc, prod_one_coe_snd, pullback.lift_snd, one_coe_eq G g]
  · rw [pullback.lift_snd]
    exact pullback.lift_snd _ _ _

abbrev fstPt : SchemeHomOver (prodStr g g) g := ⟨pullback.fst g g, rfl⟩
abbrev sndPt : SchemeHomOver (prodStr g g) g := ⟨pullback.snd g g, pullback_snd_comp_eq_prodStr g g⟩
abbrev addPt : SchemeHomOver (prodStr g g) g := ⟨addMor g G, addMor_over g G⟩

include hN hrig in

theorem nonempty_pullback_rigSection_theta :
    Nonempty ((Scheme.Modules.pullback (rigSection (prodStr g g) g ((G.prod G).one (𝟙 _)))).obj (theta g G N₀) ≅ 𝟙_ _) := by

  let s : B ⟶ pullback g g := pullback.lift (G.one g).1 (idPt g).1 ((G.one g).2.trans (idPt g).2.symm)
  have hs : ∀ (u : pullback g g ⟶ B) (hu : pullback.lift (G.one g).1 (G.one g).1 rfl ≫ u = (G.one g).1)
      (w : (pullback.fst (prodStr g g) g ≫ u) ≫ g = pullback.snd (prodStr g g) g ≫ g),
      rigSection (prodStr g g) g ((G.prod G).one (𝟙 _)) ≫ pullback.lift (pullback.fst (prodStr g g) g ≫ u) (pullback.snd (prodStr g g) g) w = s := by
    intro u hu w
    rw [rigSection_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hu, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]; rfl
  have hadd : pullback.lift (G.one g).1 (G.one g).1 rfl ≫ addMor g G = (G.one g).1 := by
    have := lift_addMor G (G.one g) (G.one g)
    rw [G.one_mul] at this
    exact this
  obtain ⟨e⟩ := nonempty_pullback_theta g G N₀ hN _ s s s (hs _ hadd _) (hs _ (pullback.lift_fst _ _ _) _)
    (hs _ (pullback.lift_snd _ _ _) _)
  obtain ⟨u⟩ := nonempty_mumford_one_left G N₀ hN hrig (idPt g)
  exact ⟨e ≪≫ triple_iso_unit u u u⟩

include hN hrig in

theorem face₁ :
    LocIsoOnBase (prodStr g g)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (G.one (prodStr g g)).1 (pullback.fst g g) (by rw [(G.one _).2]))
          (pullback.snd g g)
          (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition))).obj (theta g G N₀)) (𝟙_ _) := by
  let W : pullback g g ⟶ pullback g g := pullback.lift (fstPt g).1 (sndPt g).1 ((fstPt g).2.trans (sndPt g).2.symm)
  let E : pullback g g ⟶ pullback g g :=
    pullback.lift (G.one (prodStr g g)).1 (sndPt g).1 ((G.one (prodStr g g)).2.trans (sndPt g).2.symm)
  have hα : pullback.lift (pullback.lift (G.one (prodStr g g)).1 (pullback.fst g g) (by rw [(G.one _).2])) (pullback.snd g g)
        (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition) ≫ aMap g G = W := by
    apply pullback.hom_ext
    · rw [Category.assoc, aMap_fst, ← Category.assoc, pullback.lift_fst]
      have := lift_addMor G (G.one (prodStr g g)) (fstPt g)
      rw [G.one_mul] at this
      rw [pullback.lift_fst]; exact this
    · rw [Category.assoc, aMap_snd, pullback.lift_snd, pullback.lift_snd]
  have hβ : pullback.lift (pullback.lift (G.one (prodStr g g)).1 (pullback.fst g g) (by rw [(G.one _).2])) (pullback.snd g g)
        (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition) ≫ b1Map g = E := by
    apply pullback.hom_ext
    · rw [Category.assoc, b1Map_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, b1Map_snd, pullback.lift_snd, pullback.lift_snd]
  have hγ : pullback.lift (pullback.lift (G.one (prodStr g g)).1 (pullback.fst g g) (by rw [(G.one _).2])) (pullback.snd g g)
        (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition) ≫ b2Map g = W := by
    apply pullback.hom_ext
    · rw [Category.assoc, b2Map_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, b2Map_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨e⟩ := nonempty_pullback_theta g G N₀ hN _ W E W hα hβ hγ
  obtain ⟨u⟩ := nonempty_mumford_one_left G N₀ hN hrig (sndPt g)
  exact locIsoOnBase_unit_of_iso _ (e ≪≫ tensor_dual_dual_iso_left ((isInvertible_mumford G N₀ hN).pullback W) u)

include hN hrig in

theorem face₂ :
    LocIsoOnBase (prodStr g g)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst g g) (G.one (prodStr g g)).1 (by rw [(G.one _).2]))
          (pullback.snd g g)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj (theta g G N₀)) (𝟙_ _) := by
  let W : pullback g g ⟶ pullback g g := pullback.lift (fstPt g).1 (sndPt g).1 ((fstPt g).2.trans (sndPt g).2.symm)
  let E : pullback g g ⟶ pullback g g :=
    pullback.lift (G.one (prodStr g g)).1 (sndPt g).1 ((G.one (prodStr g g)).2.trans (sndPt g).2.symm)
  have hα : pullback.lift (pullback.lift (pullback.fst g g) (G.one (prodStr g g)).1 (by rw [(G.one _).2])) (pullback.snd g g)
        (by rw [pullback.lift_fst_assoc]; exact pullback.condition) ≫ aMap g G = W := by
    apply pullback.hom_ext
    · rw [Category.assoc, aMap_fst, ← Category.assoc, pullback.lift_fst]
      have := lift_addMor G (fstPt g) (G.one (prodStr g g))
      rw [G.mul_one] at this
      rw [pullback.lift_fst]; exact this
    · rw [Category.assoc, aMap_snd, pullback.lift_snd, pullback.lift_snd]
  have hβ : pullback.lift (pullback.lift (pullback.fst g g) (G.one (prodStr g g)).1 (by rw [(G.one _).2])) (pullback.snd g g)
        (by rw [pullback.lift_fst_assoc]; exact pullback.condition) ≫ b1Map g = W := by
    apply pullback.hom_ext
    · rw [Category.assoc, b1Map_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, b1Map_snd, pullback.lift_snd, pullback.lift_snd]
  have hγ : pullback.lift (pullback.lift (pullback.fst g g) (G.one (prodStr g g)).1 (by rw [(G.one _).2])) (pullback.snd g g)
        (by rw [pullback.lift_fst_assoc]; exact pullback.condition) ≫ b2Map g = E := by
    apply pullback.hom_ext
    · rw [Category.assoc, b2Map_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, b2Map_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨e⟩ := nonempty_pullback_theta g G N₀ hN _ W W E hα hβ hγ
  obtain ⟨u⟩ := nonempty_mumford_one_left G N₀ hN hrig (sndPt g)
  exact locIsoOnBase_unit_of_iso _ (e ≪≫ tensor_dual_dual_iso_right ((isInvertible_mumford G N₀ hN).pullback W) u)

include hN hrig in

theorem face₃ :
    LocIsoOnBase (prodStr g g)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (G.one (prodStr g g)).1 (by rw [Category.id_comp, (G.one _).2]))).obj (theta g G N₀)) (𝟙_ _) := by
  have hα : pullback.lift (𝟙 _) (G.one (prodStr g g)).1 (by rw [Category.id_comp, (G.one _).2]) ≫ aMap g G =
      pullback.lift (addPt g G).1 (G.one (prodStr g g)).1 ((addPt g G).2.trans (G.one (prodStr g g)).2.symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, aMap_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, aMap_snd, pullback.lift_snd, pullback.lift_snd]
  have hβ : pullback.lift (𝟙 _) (G.one (prodStr g g)).1 (by rw [Category.id_comp, (G.one _).2]) ≫ b1Map g =
      pullback.lift (fstPt g).1 (G.one (prodStr g g)).1 ((fstPt g).2.trans (G.one (prodStr g g)).2.symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, b1Map_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, b1Map_snd, pullback.lift_snd, pullback.lift_snd]
  have hγ : pullback.lift (𝟙 _) (G.one (prodStr g g)).1 (by rw [Category.id_comp, (G.one _).2]) ≫ b2Map g =
      pullback.lift (sndPt g).1 (G.one (prodStr g g)).1 ((sndPt g).2.trans (G.one (prodStr g g)).2.symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, b2Map_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, b2Map_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨e⟩ := nonempty_pullback_theta g G N₀ hN _ _ _ _ hα hβ hγ
  obtain ⟨u₁⟩ := nonempty_mumford_one_right G N₀ hN hrig (addPt g G)
  obtain ⟨u₂⟩ := nonempty_mumford_one_right G N₀ hN hrig (fstPt g)
  obtain ⟨u₃⟩ := nonempty_mumford_one_right G N₀ hN hrig (sndPt g)
  exact locIsoOnBase_unit_of_iso _ (e ≪≫ triple_iso_unit u₁ u₂ u₃)

end theta

end W1a
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified.W1a"

open W1a in
theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) :
    ∃ M : RigidifiedLineBundle (prodStr (pullback.snd f ι) (pullback.snd f ι)) (((L.baseChange ι).prod (L.baseChange ι)).one (𝟙 (Spec (CommRingCat.of R)))) (pullback.snd f ι),
      Nonempty (M.L ≅ ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L))))) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (by rw [((L.baseChange ι).one _).2]))
            (pullback.snd (pullback.snd f ι) (pullback.snd f ι))
            (by rw [pullback.lift_fst_assoc, ((L.baseChange ι).one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst (pullback.snd f ι) (pullback.snd f ι)) ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (by rw [((L.baseChange ι).one _).2]))
            (pullback.snd (pullback.snd f ι) (pullback.snd f ι))
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr (pullback.snd f ι) (pullback.snd f ι))
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) ((L.baseChange ι).one (prodStr (pullback.snd f ι) (pullback.snd f ι))).1 (by rw [Category.id_comp, ((L.baseChange ι).one _).2]))).obj M.L) (𝟙_ _) := by

  have hone : ((L.baseChange ι).one (𝟙 _)).1 = rigSection f ι (L.one (𝟙 _)) := by
    apply pullback.hom_ext
    · rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      change _ = pullback.lift _ _ _ ≫ _
      rw [pullback.lift_fst]
      exact (congrArg Subtype.val (L.one_natural (𝟙 _) (𝟙 _ ≫ ι) ι (by rw [Category.comp_id, Category.id_comp]))).symm
    · rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
      change _ = pullback.lift _ _ _ ≫ _
      rw [pullback.lift_snd]
  have hrig : Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).one (𝟙 _)).1).obj N.L ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullbackCongr hone).app N.L ≪≫ N.rigidified.some ≪≫ eqToIso (Scheme.Modules.tensorUnit_eq).symm⟩
  refine ⟨⟨W1a.theta (pullback.snd f ι) (L.baseChange ι) N.L, W1a.isInvertible_theta _ _ _ N.isInvertible,
      ⟨(W1a.nonempty_pullback_rigSection_theta _ _ _ N.isInvertible hrig).some ≪≫ eqToIso Scheme.Modules.tensorUnit_eq⟩⟩,
    ⟨Iso.refl _⟩, W1a.face₁ _ _ _ N.isInvertible hrig, W1a.face₂ _ _ _ N.isInvertible hrig, W1a.face₃ _ _ _ N.isInvertible hrig⟩

end
end S_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_rigidifiedLineBundle_iso_thetaCube_and_locIsoOnBase_faces_of_rigidified (solution)
