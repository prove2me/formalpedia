-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.twoGluedSmoothCurveDegenerations_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a2b43cad-f2bd-5de6-9f3d-d11239c44b9d

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.isoOfEq_hom_ι SmoothOfRelativeDimension IsProper Scheme.Hom GeometricallyIntegral Scheme.homeoOfIso Spec Scheme Smooth IsOpenImmersion IsClosedImmersion IsReduced Scheme.Hom.comp_preimage isReduced_of_isOpenImmersion"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "sectionFibrePoint exists_fibreIso_hom_comp_eq"
namespace N13Transport
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem exists_fibreIso_baseChange {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (baseChange R c A) x' ≅ pullback c (x' ≫ specMap R A),
      φ.hom ≫ pullback.snd c (x' ≫ specMap R A) = pullback.snd (baseChange R c A) x' ∧
      φ.hom ≫ pullback.fst c (x' ≫ specMap R A) = pullback.fst (baseChange R c A) x' ≫ pullback.fst c (specMap R A) := by
  obtain ⟨φ, h1, h2, -⟩ := exists_fibreIso_hom_comp_eq c (specMap R A) x' (x' ≫ specMap R A) rfl
  exact ⟨φ, h1, h2⟩

end AlgebraicGeometry.RelPicard.N13Transport

open AlgebraicGeometry.RelPicard.N13Transport in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1))) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), ¬ Smooth (pullback.snd (baseChange R c A) s') →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (baseChange R c A) s')) (i₂ : SchemeHomOver c₂ (pullback.snd (baseChange R c A) s'))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (baseChange R c A) s'), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
          connectedComponentIn ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
            (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
          ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) \
            connectedComponentIn ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
              (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback (baseChange R c A) s').Opens, (W₁ : Set ↥(pullback (baseChange R c A) s')) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (baseChange R c A) s').Opens, (W₂ : Set ↥(pullback (baseChange R c A) s')) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by
  intro k _ _ s' hns
  obtain ⟨φ, hφ2, hφ1⟩ := exists_fibreIso_baseChange c A s'

  have hns0 : ¬ Smooth (pullback.snd c (s' ≫ specMap R A)) := by
    intro h
    apply hns
    rw [← hφ2]
    infer_instance
  obtain ⟨C₁, C₂, c₁, c₂, hp₁, hsm₁, hgi₁, hp₂, hsm₂, hgi₂, i₁, i₂, hci₁, hci₂, n, hjs, hcr, hn, hn0, hεmem, hUeq, hUtr₁, hUtr₂,
    ⟨W₁, hW₁, hW₁oi⟩, ⟨W₂, hW₂, hW₂oi⟩⟩ := hbad k (s' ≫ specMap R A) hns0
  haveI := hci₁; haveI := hci₂; haveI := hcr

  let e : ↥(pullback (baseChange R c A) s') ≃ₜ ↥(pullback c (s' ≫ specMap R A)) := Scheme.homeoOfIso φ
  have he : ∀ y : ↥(pullback (baseChange R c A) s'), e y = φ.hom.base y := fun _ => rfl
  have hesymm : ∀ x : ↥(pullback c (s' ≫ specMap R A)), e.symm x = φ.inv.base x := fun _ => rfl
  have hcompb : ∀ {Y : Scheme.{u}} (f : Y ⟶ pullback c (s' ≫ specMap R A)) (y : ↥Y),
      (f ≫ φ.inv).base y = φ.inv.base (f.base y) := fun _ _ => rfl
  have hrange : ∀ {Y : Scheme.{u}} (f : Y ⟶ pullback c (s' ≫ specMap R A)),
      Set.range (f ≫ φ.inv).base = e ⁻¹' Set.range f.base := by
    intro Y f
    have : ((f ≫ φ.inv).base : ↥Y → ↥(pullback (baseChange R c A) s')) = e.symm ∘ f.base := funext fun y => hcompb f y
    rw [this, Set.range_comp, Homeomorph.image_symm]

  have hV' : pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      = φ.hom ⁻¹ᵁ (pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ1]
  have hV'set : ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
      (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
      e ⁻¹' ((pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s' ≫ specMap R A)).Opens) :
        Set ↥(pullback c (s' ≫ specMap R A))) := by
    rw [hV']; rfl

  have hsec : (sectionFibrePoint (sectionBaseChange A ε) s').1 ≫ φ.hom = (sectionFibrePoint ε (s' ≫ specMap R A)).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ1]
      show (sectionFibrePoint (sectionBaseChange A ε) s').1 ≫ pullback.fst (baseChange R c A) s' ≫
          pullback.fst c (specMap R A) = (sectionFibrePoint ε (s' ≫ specMap R A)).1 ≫ pullback.fst c (s' ≫ specMap R A)
      simp only [sectionFibrePoint, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, sectionBaseChange_coe_fst]
    · rw [Category.assoc, hφ2]
      simp only [sectionFibrePoint, pullback.lift_snd]
  have hsecpt : φ.inv.base (((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k))
      = ((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k) := by
    rw [← hsec]
    exact e.symm_apply_apply _
  have hsecpt' : e (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) =
      ((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k) := by
    rw [← hsecpt, ← hesymm, e.apply_symm_apply]

  have hpre : ∀ {Y : Scheme.{u}} (f : Y ⟶ pullback c (s' ≫ specMap R A)) (W : (pullback c (s' ≫ specMap R A)).Opens),
      (f ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W) = f ⁻¹ᵁ W := by
    intro Y f W
    rw [← Scheme.Hom.comp_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

  set V : Set ↥(pullback c (s' ≫ specMap R A)) :=
    ((pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s' ≫ specMap R A)).Opens) : Set ↥(pullback c (s' ≫ specMap R A)))
    with hVdef
  set pt := ((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k) with hptdef
  have hcc : e ⁻¹' connectedComponentIn V pt =
      connectedComponentIn (e ⁻¹' V) (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) := by
    rw [← hsecpt, ← hesymm]
    by_cases hx : pt ∈ V
    · rw [← Homeomorph.image_symm]
      exact Homeomorph.image_connectedComponentIn _ hx
    · rw [connectedComponentIn_eq_empty hx, Set.preimage_empty, connectedComponentIn_eq_empty]
      intro h
      apply hx
      have : e (e.symm pt) ∈ V := h
      rwa [e.apply_symm_apply] at this

  have hsnd : φ.inv ≫ pullback.snd (baseChange R c A) s' = pullback.snd c (s' ≫ specMap R A) := by
    rw [← hφ2, φ.inv_hom_id_assoc]
  let i₁' : SchemeHomOver c₁ (pullback.snd (baseChange R c A) s') := ⟨i₁.1 ≫ φ.inv, by rw [Category.assoc, hsnd, i₁.2]⟩
  let i₂' : SchemeHomOver c₂ (pullback.snd (baseChange R c A) s') := ⟨i₂.1 ≫ φ.inv, by rw [Category.assoc, hsnd, i₂.2]⟩

  let m : pullback (i₁.1 ≫ φ.inv) (i₂.1 ≫ φ.inv) ⟶ pullback i₁.1 i₂.1 :=
    pullback.map (i₁.1 ≫ φ.inv) (i₂.1 ≫ φ.inv) i₁.1 i₂.1 (𝟙 _) (𝟙 _) φ.hom (by simp) (by simp)
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  have hmfst : m ≫ pullback.fst i₁.1 i₂.1 = pullback.fst (i₁.1 ≫ φ.inv) (i₂.1 ≫ φ.inv) := by
    simp only [m, pullback.lift_fst, Category.comp_id]

  refine ⟨C₁, C₂, c₁, c₂, hp₁, hsm₁, hgi₁, hp₂, hsm₂, hgi₂, i₁', i₂', inferInstance, inferInstance, n,
    ?_, ?_, ?_, hn0, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro z
    rcases hjs (e z) with h | h
    · left; show z ∈ Set.range (i₁.1 ≫ φ.inv).base; rw [hrange]; exact h
    · right; show z ∈ Set.range (i₂.1 ≫ φ.inv).base; rw [hrange]; exact h

  · show IsReduced (pullback (i₁.1 ≫ φ.inv) (i₂.1 ≫ φ.inv))
    exact isReduced_of_isOpenImmersion m

  · show Nat.card ↥(pullback (i₁.1 ≫ φ.inv) (i₂.1 ≫ φ.inv)) = n
    rw [← hn]
    exact Nat.card_congr (Scheme.homeoOfIso (asIso m)).toEquiv

  · show ((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k) ∈
      Set.range (i₁.1 ≫ φ.inv).base \ Set.range (i₂.1 ≫ φ.inv).base
    rw [hrange, hrange, ← Set.preimage_diff, Set.mem_preimage, hsecpt']
    exact hεmem

  · show _ = (Set.range (pullback.fst (i₁.1 ≫ φ.inv) (i₂.1 ≫ φ.inv) ≫ i₁.1 ≫ φ.inv).base)ᶜ
    rw [hV'set, ← hmfst]
    have hr : Set.range ((m ≫ pullback.fst i₁.1 i₂.1) ≫ i₁.1 ≫ φ.inv).base =
        Set.range ((pullback.fst i₁.1 i₂.1 ≫ i₁.1) ≫ φ.inv).base := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨m.base y, rfl⟩
      · rintro ⟨y', rfl⟩
        obtain ⟨y, hy⟩ := (Scheme.homeoOfIso (asIso m)).surjective y'
        refine ⟨y, ?_⟩
        change φ.inv.base (i₁.1.base ((pullback.fst i₁.1 i₂.1).base (m.base y))) =
          φ.inv.base (i₁.1.base ((pullback.fst i₁.1 i₂.1).base y'))
        rw [← hy]
        rfl
    show e ⁻¹' V = _
    rw [hr, hrange, ← Set.preimage_compl, ← hUeq]

  · show Set.range (i₁.1 ≫ φ.inv).base ∩ _ = _
    rw [hrange, hV'set, ← Set.preimage_inter]
    show e ⁻¹' (Set.range i₁.1.base ∩ V) = _
    rw [hUtr₁, hcc]

  · show Set.range (i₂.1 ≫ φ.inv).base ∩ _ = _
    rw [hrange, hV'set, ← Set.preimage_inter]
    show e ⁻¹' (Set.range i₂.1.base ∩ V) = e ⁻¹' V \ _
    rw [hUtr₂, Set.preimage_diff, hcc]

  · refine ⟨φ.hom ⁻¹ᵁ W₁, ?_, ?_⟩
    · show e ⁻¹' (W₁ : Set ↥(pullback c (s' ≫ specMap R A))) = (Set.range (i₂.1 ≫ φ.inv).base)ᶜ
      rw [hW₁, Set.preimage_compl, hrange]
    · show IsOpenImmersion (((i₁.1 ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₁)).ι ≫ i₁.1 ≫ φ.inv)
      have heq : (i₁.1 ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₁) = i₁.1 ⁻¹ᵁ W₁ := hpre i₁.1 W₁
      have : ((i₁.1 ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₁)).ι ≫ i₁.1 ≫ φ.inv
          = (C₁.isoOfEq heq).hom ≫ ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1) ≫ φ.inv := by
        rw [← Scheme.isoOfEq_hom_ι C₁ heq]
        simp only [Category.assoc]
      rw [this]
      haveI := hW₁oi
      infer_instance

  · refine ⟨φ.hom ⁻¹ᵁ W₂, ?_, ?_⟩
    · show e ⁻¹' (W₂ : Set ↥(pullback c (s' ≫ specMap R A))) = (Set.range (i₁.1 ≫ φ.inv).base)ᶜ
      rw [hW₂, Set.preimage_compl, hrange]
    · show IsOpenImmersion (((i₂.1 ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₂)).ι ≫ i₂.1 ≫ φ.inv)
      have heq : (i₂.1 ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₂) = i₂.1 ⁻¹ᵁ W₂ := hpre i₂.1 W₂
      have : ((i₂.1 ≫ φ.inv) ⁻¹ᵁ (φ.hom ⁻¹ᵁ W₂)).ι ≫ i₂.1 ≫ φ.inv
          = (C₂.isoOfEq heq).hom ≫ ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1) ≫ φ.inv := by
        rw [← Scheme.isoOfEq_hom_ι C₂ heq]
        simp only [Category.assoc]
      rw [this]
      haveI := hW₂oi
      infer_instance

end S_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange (solution)
