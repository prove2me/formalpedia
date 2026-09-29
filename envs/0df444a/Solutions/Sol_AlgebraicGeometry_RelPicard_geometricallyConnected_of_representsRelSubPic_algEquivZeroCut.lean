-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/158323f9-ce24-5a54-897e-c092b43e5fdd

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral pointOfClosedPoint_apply Scheme.Pullback.range_map GeometricallyIrreducible pointOfClosedPoint Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp Scheme.Modules.pullbackCongr GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Modules.pullbackId Scheme.Modules GeometricallyConnected Scheme.Hom.comp_apply geometrically range_eq_univ Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso FibrewiseAlgEquivZero.pullback algEquivZeroCut rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso"
namespace Connected
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}

noncomputable def zeroPt {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    Spec (CommRingCat.of K) ⟶ pullback D.toBase y :=
  pullback.lift (y ≫ D.zeroSection) (𝟙 _) (by rw [Category.assoc, D.zeroSection_toBase]; simp)

@[scoped simp] theorem zeroPt_snd {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    zeroPt (D := D) y ≫ pullback.snd D.toBase y = 𝟙 _ := pullback.lift_snd _ _ _

section Compare

variable {k : Type u} [Field k] (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  {T' : Scheme.{u}} (hT : T' ⟶ Spec (CommRingCat.of k))

noncomputable abbrev Fib (c : C ⟶ Spec (CommRingCat.of R)) := pullback (pullback.snd c y) (𝟙 (Spec (CommRingCat.of k)))

noncomputable def toFibProd (c : C ⟶ Spec (CommRingCat.of R)) :
    pullback c (hT ≫ y) ⟶ pullback (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) hT :=
  pullback.lift
    (pullback.lift (pullback.lift (pullback.fst c (hT ≫ y)) (pullback.snd c (hT ≫ y) ≫ hT)
        (by rw [pullback.condition, Category.assoc]))
      (pullback.snd c (hT ≫ y) ≫ hT) (by rw [pullback.lift_snd, Category.comp_id]))
    (pullback.snd c (hT ≫ y))
    (by simp only [fibreAt, pullback.lift_snd])

noncomputable def ofFibProd (c : C ⟶ Spec (CommRingCat.of R)) :
    pullback (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) hT ⟶ pullback c (hT ≫ y) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst c y)
    (pullback.snd _ _)
    (by
      have h1 : pullback.fst c y ≫ c = pullback.snd c y ≫ y := pullback.condition
      have h2 : pullback.fst (pullback.snd c y) (𝟙 (Spec (CommRingCat.of k))) ≫ pullback.snd c y =
          fibreAt c y (𝟙 _) := by
        rw [fibreAt, pullback.condition, Category.comp_id]
      have h3 : pullback.fst (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) hT ≫ fibreAt c y (𝟙 _) =
          pullback.snd _ _ ≫ hT := pullback.condition
      rw [Category.assoc, Category.assoc, h1, ← Category.assoc (pullback.fst (pullback.snd c y) _), h2,
        ← Category.assoc, h3, Category.assoc])

@[scoped simp] theorem toFibProd_snd (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibProd y hT c ≫ pullback.snd _ _ = pullback.snd c (hT ≫ y) := by
  unfold toFibProd; rw [pullback.lift_snd]
@[scoped simp] theorem toFibProd_fst_snd (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibProd y hT c ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd c (hT ≫ y) ≫ hT := by
  unfold toFibProd; rw [pullback.lift_fst_assoc, pullback.lift_snd]
@[scoped simp] theorem toFibProd_fst_fst_fst (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibProd y hT c ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst c y = pullback.fst c (hT ≫ y) := by
  unfold toFibProd; rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, pullback.lift_fst]
@[scoped simp] theorem toFibProd_fst_fst_snd (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibProd y hT c ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd c y = pullback.snd c (hT ≫ y) ≫ hT := by
  unfold toFibProd; rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, pullback.lift_snd]
@[scoped simp] theorem ofFibProd_fst (c : C ⟶ Spec (CommRingCat.of R)) :
    ofFibProd y hT c ≫ pullback.fst c (hT ≫ y) = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst c y := by
  unfold ofFibProd; rw [pullback.lift_fst]
@[scoped simp] theorem ofFibProd_snd (c : C ⟶ Spec (CommRingCat.of R)) :
    ofFibProd y hT c ≫ pullback.snd c (hT ≫ y) = pullback.snd _ _ := by
  unfold ofFibProd; rw [pullback.lift_snd]

theorem toFibProd_ofFibProd (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibProd y hT c ≫ ofFibProd y hT c = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ofFibProd_fst, toFibProd_fst_fst_fst, Category.id_comp]
  · rw [Category.assoc, ofFibProd_snd, toFibProd_snd, Category.id_comp]

theorem ofFibProd_toFibProd (c : C ⟶ Spec (CommRingCat.of R)) :
    ofFibProd y hT c ≫ toFibProd y hT c = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, toFibProd_fst_fst_fst, ofFibProd_fst]; simp
      · rw [Category.assoc, Category.assoc, Category.assoc, toFibProd_fst_fst_snd, ← Category.assoc, ofFibProd_snd,
          Category.id_comp, Category.assoc]

        rw [pullback.condition (f := pullback.snd c y) (g := 𝟙 (Spec (CommRingCat.of k))), Category.comp_id]
        exact pullback.condition.symm
    · rw [Category.assoc, Category.assoc, toFibProd_fst_snd, ← Category.assoc, ofFibProd_snd, Category.id_comp]
      exact pullback.condition.symm
  · rw [Category.assoc, toFibProd_snd, ofFibProd_snd, Category.id_comp]

noncomputable def fibProdIso (c : C ⟶ Spec (CommRingCat.of R)) :
    pullback c (hT ≫ y) ≅ pullback (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) hT :=
  ⟨toFibProd y hT c, ofFibProd y hT c, toFibProd_ofFibProd y hT c, ofFibProd_toFibProd y hT c⟩

end Compare

section Helpers

theorem connectedSpace_of_geometricallyIntegral {k : Type u} [Field k] {T' : Scheme.{u}}
    (hT : T' ⟶ Spec (CommRingCat.of k)) [GeometricallyIntegral hT] : ConnectedSpace ↥T' := by
  haveI : IrreducibleSpace ↥T' := GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := hT)
  infer_instance

variable {k : Type u} [Field k]

theorem nonempty_ofInvertible_iso_of_field (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (N : (pullback c y).Modules) (hN : Scheme.Modules.IsInvertible N) :
    Nonempty ((RigidifiedLineBundle.ofInvertible (ε := ε) N hN).L ≅ N) := by
  obtain ⟨u⟩ := (((hN.pullback (rigSection c y ε)).dual).1).nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨(Iso.refl N ⊗ᵢ ((Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)) ≪≫ ρ_ N⟩

noncomputable def toFibOne (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (c : C ⟶ Spec (CommRingCat.of R)) :
    pullback c y ⟶ pullback (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) (𝟙 (Spec (CommRingCat.of k))) :=
  pullback.lift (pullback.lift (𝟙 _) (pullback.snd c y) (by simp)) (pullback.snd c y)
    (by simp only [fibreAt, pullback.lift_snd, Category.comp_id])

@[scoped simp] theorem toFibOne_fst_fst (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibOne y c ≫ pullback.fst _ _ ≫ pullback.fst _ _ = 𝟙 _ := by
  unfold toFibOne; rw [pullback.lift_fst_assoc, pullback.lift_fst]
@[scoped simp] theorem toFibOne_fst_snd (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibOne y c ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd c y := by
  unfold toFibOne; rw [pullback.lift_fst_assoc, pullback.lift_snd]
@[scoped simp] theorem toFibOne_snd (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (c : C ⟶ Spec (CommRingCat.of R)) :
    toFibOne y c ≫ pullback.snd _ _ = pullback.snd c y := by
  unfold toFibOne; rw [pullback.lift_snd]

theorem baseChangeSnd_toFibProd (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {T' : Scheme.{u}} (hT : T' ⟶ Spec (CommRingCat.of k))
    (τ : SchemeHomOver y (hT ≫ y)) (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) hT) (hτ : τ.1 = t.1)
    (c : C ⟶ Spec (CommRingCat.of R)) :
    baseChangeSnd c τ ≫ toFibProd y hT c =
      toFibOne y c ≫ baseChangeSnd (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) t := by
  have ht : t.1 ≫ hT = 𝟙 _ := t.2
  have hτt : τ.1 ≫ hT = 𝟙 _ := by rw [hτ, ht]
  have e1 : toFibOne y c ≫ pullback.fst _ _ ≫ pullback.fst _ _ = 𝟙 _ := toFibOne_fst_fst y c
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, toFibProd_fst_fst_fst]
        simp only [baseChangeSnd, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, reassoc_of% e1]
      · simp only [Category.assoc, toFibProd_fst_fst_snd]
        simp only [baseChangeSnd, pullback.lift_snd_assoc, pullback.lift_fst_assoc, Category.comp_id, reassoc_of% e1]
        rw [Category.assoc, hτt, Category.comp_id]
    · simp only [Category.assoc, toFibProd_fst_snd]
      simp only [baseChangeSnd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, toFibOne_fst_snd]
      rw [Category.assoc, hτt, Category.comp_id]
  · simp only [Category.assoc, toFibProd_snd]
    simp only [baseChangeSnd, pullback.lift_snd, hτ]
    rw [← Category.assoc, toFibOne_snd]

end Helpers

theorem mem_connectedComponent_zero (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] {k : Type u} [Field k] [IsAlgClosed k]
    (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (x : ↥(pullback D.toBase y)) (hx : x ∈ closedPoints ↥(pullback D.toBase y)) :
    x ∈ connectedComponent (zeroPt (D := D) y (IsLocalRing.closedPoint k)) := by
  classical
  let p := pullback.snd D.toBase y
  let q := pullback.fst D.toBase y
  haveI : LocallyOfFiniteType p := inferInstance

  let sx : Spec (CommRingCat.of k) ⟶ pullback D.toBase y := pointOfClosedPoint p x hx
  have hsx : sx ≫ p = 𝟙 _ := pointOfClosedPoint_comp p x hx
  have hsxx : sx (IsLocalRing.closedPoint k) = x := pointOfClosedPoint_apply p x hx _
  let gx : SchemeHomOver y D.toBase :=
    ⟨sx ≫ q, by rw [Category.assoc, pullback.condition, ← Category.assoc, hsx, Category.id_comp]⟩
  let zPt : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase := ⟨D.zeroSection, D.zeroSection_toBase⟩
  let yPt : SchemeHomOver y (𝟙 (Spec (CommRingCat.of R))) := ⟨y, Category.comp_id y⟩
  let g0 : SchemeHomOver y D.toBase := postComp zPt yPt

  let Px : RigidifiedLineBundle c ε y := h.poincare.pullbackAlong gx
  have hPx : FibrewiseAlgEquivZero Px := FibrewiseAlgEquivZero.pullback gx h.poincare_mem
  obtain ⟨T', hT, hlft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hPx k (𝟙 _)

  let L' : (pullback c (hT ≫ y)).Modules := (Scheme.Modules.pullback (toFibProd y hT c)).obj M
  have hL' : Scheme.Modules.IsInvertible L' := hM.pullback _
  let Mrig : RigidifiedLineBundle c ε (hT ≫ y) := RigidifiedLineBundle.ofInvertible L' hL'
  have hMrig : FibrewiseAlgEquivZero Mrig := by
    intro k'' _ _ s

    let t' : T' ⟶ Spec (CommRingCat.of R) := hT ≫ y
    let js := pullback.fst (pullback.snd c t') s
    let as := fibreAt c t' s
    have hjs : js ≫ pullback.snd c t' = as ≫ s := pullback.condition

    have hcorr : Scheme.Modules.IsInvertible (rigCorrection ε t' L') := ((hL'.pullback _).dual).1
    obtain ⟨u⟩ := (hcorr.pullback s).nonempty_iso_tensorUnit_of_isLocalRing
    have iP1 : (Scheme.Modules.pullback js).obj Mrig.L ≅ (Scheme.Modules.pullback (js ≫ toFibProd y hT c)).obj M := by
      refine (Scheme.Modules.pullback js).mapIso (Iso.refl _) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M
      exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hjs).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ (Scheme.Modules.pullback as).mapIso u ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
    refine IsAlgEquivZero.of_iso iP1.symm ?_

    let κ : Spec (CommRingCat.of k'') ⟶ Spec (CommRingCat.of k) := s ≫ hT
    let T'' := pullback hT κ
    let hT'' : T'' ⟶ Spec (CommRingCat.of k'') := pullback.snd hT κ
    haveI : LocallyOfFiniteType hT := hlft
    haveI : GeometricallyIntegral hT := hgi

    let θF : pullback as hT'' ⟶ pullback (pullback.snd c y) (𝟙 (Spec (CommRingCat.of k))) :=
      pullback.fst as hT'' ≫ js ≫ toFibProd y hT c ≫ pullback.fst _ _
    have hθF : θF ≫ fibreAt c y (𝟙 _) = (pullback.snd as hT'' ≫ pullback.fst hT κ) ≫ hT := by
      simp only [θF, Category.assoc]
      rw [pullback.condition, ← Category.assoc (toFibProd y hT c), toFibProd_snd, ← Category.assoc js, hjs,
        Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
    let Θ : pullback as hT'' ⟶ pullback (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) hT :=
      pullback.lift θF (pullback.snd as hT'' ≫ pullback.fst hT κ) hθF
    let t₁'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k''))) hT'' :=
      ⟨pullback.lift s (𝟙 _) (by simp [κ]), pullback.lift_snd _ _ _⟩
    let t₀'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k''))) hT'' :=
      ⟨pullback.lift (κ ≫ t₀.1) (𝟙 _) (by rw [Category.assoc, t₀.2, Category.comp_id, Category.id_comp]), pullback.lift_snd _ _ _⟩

    have hΘ1 : baseChangeSnd as t₁'' ≫ Θ = pullback.fst as (𝟙 _) ≫ js ≫ toFibProd y hT c := by
      apply pullback.hom_ext
      · simp only [Θ, θF, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      · simp only [Θ, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, toFibProd_snd]
        rw [pullback.lift_fst]
        erw [hjs]
        rw [← Category.assoc, pullback.condition, Category.comp_id]
    let ω : pullback as (𝟙 (Spec (CommRingCat.of k''))) ⟶ pullback (fibreAt c y (𝟙 (Spec (CommRingCat.of k)))) (𝟙 _) :=
      pullback.lift (pullback.fst as (𝟙 _) ≫ js ≫ toFibProd y hT c ≫ pullback.fst _ _) (pullback.snd _ _ ≫ κ) (by
        rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (toFibProd y hT c),
          toFibProd_snd, ← Category.assoc js, hjs, Category.assoc, ← Category.assoc, pullback.condition, Category.assoc,
          Category.comp_id, Category.id_comp])
    have hΘ0 : baseChangeSnd as t₀'' ≫ Θ = ω ≫ baseChangeSnd (fibreAt c y (𝟙 _)) t₀ := by
      apply pullback.hom_ext
      · simp only [Θ, θF, ω, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      · simp only [Θ, ω, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        show pullback.snd as (𝟙 _) ≫ pullback.lift (κ ≫ t₀.1) (𝟙 _) _ ≫ pullback.fst hT κ = _
        rw [pullback.lift_fst]
    refine ⟨T'', hT'', inferInstance, inferInstance, (Scheme.Modules.pullback Θ).obj M, hM.pullback _, t₀'', t₁'', ⟨?_⟩, ⟨?_⟩⟩
    · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫ (Scheme.Modules.pullbackCongr hΘ0).app M ≪≫
        ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫ (Scheme.Modules.pullback ω).mapIso e₀ ≪≫
        Scheme.Modules.pullbackUnitIso _
    · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫ (Scheme.Modules.pullbackCongr hΘ1).app M ≪≫
        ((Scheme.Modules.pullbackComp _ _).app M).symm

  let φ : SchemeHomOver (hT ≫ y) D.toBase := h.classify (hT ≫ y) Mrig hMrig
  let φk : T' ⟶ pullback D.toBase y := pullback.lift φ.1 hT φ.2

  let τ₁ : SchemeHomOver y (hT ≫ y) := ⟨t₁.1, by rw [← Category.assoc, t₁.2, Category.id_comp]⟩
  let τ₀ : SchemeHomOver y (hT ≫ y) := ⟨t₀.1, by rw [← Category.assoc, t₀.2, Category.id_comp]⟩
  have e1' : (toFibOne y c ≫ pullback.fst _ _) ≫ pullback.fst _ _ = 𝟙 (pullback c y) := by
    rw [Category.assoc]; exact toFibOne_fst_fst y c

  have restr : ∀ (τ : SchemeHomOver y (hT ≫ y)) (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) hT), τ.1 = t.1 →
      Nonempty ((h.poincare.pullbackAlong (postComp φ τ)).L ≅
        (Scheme.Modules.pullback (toFibOne y c)).obj
          ((Scheme.Modules.pullback (baseChangeSnd (fibreAt c y (𝟙 _)) t)).obj M)) := by
    intro τ t hτ
    obtain ⟨i1⟩ := h.classify_spec (hT ≫ y) Mrig hMrig
    obtain ⟨i2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) τ hL'
    obtain ⟨i3⟩ := nonempty_ofInvertible_iso_of_field (ε := ε) y
      ((Scheme.Modules.pullback (baseChangeSnd c τ)).obj L') (hL'.pullback _)
    exact ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ τ).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c τ)).mapIso i1 ≪≫ i2 ≪≫ i3 ≪≫
      (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (baseChangeSnd_toFibProd y hT τ t hτ c)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm⟩

  have hI1 : postComp φ τ₁ = gx := by
    obtain ⟨r⟩ := restr τ₁ t₁ rfl
    refine h.ext_of_iso y _ _ ⟨r ≪≫ (Scheme.Modules.pullback _).mapIso e₁ ≪≫ ?_⟩
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr e1').app _ ≪≫ (Scheme.Modules.pullbackId _).app _
  have hI0 : postComp φ τ₀ = g0 := by
    obtain ⟨r⟩ := restr τ₀ t₀ rfl
    obtain ⟨z⟩ := h.zero
    refine h.ext_of_iso y _ _ ⟨r ≪≫ (Scheme.Modules.pullback _).mapIso e₀ ≪≫ Scheme.Modules.pullbackUnitIso _ ≪≫ ?_⟩
    exact ((Scheme.Modules.pullbackCongr (baseChangeSnd_comp c zPt yPt).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c yPt)).mapIso z ≪≫
      Scheme.Modules.pullbackUnitIso _).symm
  have h1 : φk (t₁.1 (IsLocalRing.closedPoint k)) = x := by
    have : t₁.1 ≫ φk = sx := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        exact congrArg Subtype.val hI1
      · rw [Category.assoc, pullback.lift_snd, hsx]; exact t₁.2
    rw [← Scheme.Hom.comp_apply, this, hsxx]
  have h0 : φk (t₀.1 (IsLocalRing.closedPoint k)) = zeroPt (D := D) y (IsLocalRing.closedPoint k) := by
    have : t₀.1 ≫ φk = zeroPt (D := D) y := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, zeroPt, pullback.lift_fst]
        exact congrArg Subtype.val hI0
      · rw [Category.assoc, pullback.lift_snd, zeroPt_snd]; exact t₀.2
    rw [← Scheme.Hom.comp_apply, this]

  haveI : GeometricallyIntegral hT := hgi
  haveI : ConnectedSpace ↥T' := connectedSpace_of_geometricallyIntegral hT
  have hpre : _root_.IsPreconnected (Set.range φk) := isPreconnected_range φk.continuous
  exact hpre.subset_connectedComponent ⟨_, h0⟩ ⟨_, h1⟩

theorem connectedSpace_pullback_of_isAlgClosed (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] {k : Type u} [Field k] [IsAlgClosed k]
    (y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ConnectedSpace ↥(pullback D.toBase y) := by
  haveI : LocallyOfFiniteType (pullback.snd D.toBase y) := inferInstance
  haveI : JacobsonSpace ↥(pullback D.toBase y) := LocallyOfFiniteType.jacobsonSpace (pullback.snd D.toBase y)
  rw [connectedSpace_iff_connectedComponent]
  refine ⟨zeroPt (D := D) y (IsLocalRing.closedPoint k), Set.eq_univ_of_univ_subset ?_⟩
  rw [← closure_closedPoints (X := ↥(pullback D.toBase y))]
  exact closure_minimal (fun x hx => mem_connectedComponent_zero h y x hx) isClosed_connectedComponent

theorem connectedSpace_pullback (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] {K : Type u} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    ConnectedSpace ↥(pullback D.toBase y) := by
  let k : Type u := AlgebraicClosure K
  let j : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K k))
  haveI := connectedSpace_pullback_of_isAlgClosed h (j ≫ y)

  let m : pullback D.toBase (j ≫ y) ⟶ pullback D.toBase y :=
    pullback.map _ _ _ _ (𝟙 _) j (𝟙 _) (by simp) (by simp)
  haveI : Surjective j := inferInstance
  have hm : Function.Surjective m := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_map _ _ _ _ (𝟙 _) j (𝟙 _) (by simp) (by simp)]
    simp [Set.range_eq_univ.mpr j.surjective]
  exact hm.connectedSpace m.continuous

end AlgebraicGeometry.RelPicard.Connected
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry.RelPicard.Connected"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral pointOfClosedPoint_apply Scheme.Pullback.range_map GeometricallyIrreducible pointOfClosedPoint Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp Scheme.Modules.pullbackCongr GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Modules.pullbackId Scheme.Modules GeometricallyConnected Scheme.Hom.comp_apply geometrically range_eq_univ Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso" namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso FibrewiseAlgEquivZero.pullback algEquivZeroCut rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso" end AlgebraicGeometry.RelPicard
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelPicard" in
open AlgebraicGeometry.RelPicard.Connected in
theorem AlgebraicGeometry.RelPicard.geometricallyConnected_of_representsRelSubPic_algEquivZeroCut'
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    GeometricallyConnected D.toBase := by
  refine ⟨fun K _ y Z fst snd hP => ?_⟩
  haveI := connectedSpace_pullback h y
  exact (Scheme.homeoOfIso hP.isoPullback).symm.connectedSpace_iff.mp inferInstance

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian in

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    GeometricallyConnected D.toBase :=
  AlgebraicGeometry.RelPicard.geometricallyConnected_of_representsRelSubPic_algEquivZeroCut' R c ε D h

end S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut (solution)
