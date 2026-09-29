-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isOpenImmersion_of_functionField_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5e4847ea-56d1-59f9-bbd2-5f0fcd6b12d2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι IsOpenImmersion.lift Scheme.PartialMap Scheme.fromSpecStalk_closedPoint Spec.map_comp_assoc Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.isoImage_inv_ι_assoc Scheme.SpecMap_stalkSpecializes_fromSpecStalk LocallyOfFiniteType Spec IsIntegral Scheme.Opens.fromSpecStalkOfMem Spec.map Scheme Scheme.Opens.fromSpecStalkOfMem_ι Scheme.Hom.resLE_map Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk IsOpenImmersion Spec.map_injective Scheme.PartialMap.mem_domain_ofFromSpecStalk Scheme.homOfLE_homOfLE Scheme.Hom.isoImage_inv_ι Scheme.PartialMap.ofFromSpecStalk_comp Scheme.Opens.fromSpecStalkOfMem_ι_assoc Spec.map_id Scheme.Hom.map_resLE Scheme.SpecMap_stalkMap_fromSpecStalk Spec_closedPoint Scheme.Opens Scheme.homOfLE_ι spread_out_unique_of_isGermInjective' IsOpenImmersion.lift_fac Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply"
p2m_open "AlgebraicGeometry"

theorem isOpenImmersion_ι_comp_of_inverse_on_opens {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Y.Opens) (gB : (B : Scheme.{u}) ⟶ X)
    (W : X.Opens) (hWB : W ≤ f ⁻¹ᵁ B) (hb : f.resLE B W hWB ≫ gB = W.ι)
    (W' : Y.Opens) (hW'B : W' ≤ B) (ha : Y.homOfLE hW'B ≫ gB ≫ f = W'.ι) :
    IsOpenImmersion ((W ⊓ f ⁻¹ᵁ W').ι ≫ f) := by
  classical
  set A : X.Opens := W ⊓ f ⁻¹ᵁ W' with hAdef

  have hb' : ∀ x : (W : Scheme.{u}), gB.base (f.resLE B W hWB |>.base x) = x.1 := fun x => by
    have := congrArg (fun k : (W : Scheme.{u}) ⟶ X => k.base x) hb
    simpa using this
  have ha' : ∀ y : (W' : Scheme.{u}), f.base (gB.base ((Y.homOfLE hW'B).base y)) = y.1 := fun y => by
    have := congrArg (fun k : (W' : Scheme.{u}) ⟶ Y => k.base y) ha
    simpa using this

  set A' : Y.Opens := W' ⊓ B.ι ''ᵁ (gB ⁻¹ᵁ A) with hA'def
  have hA'B : A' ≤ B := fun y hy => hW'B hy.1
  have hA'W' : A' ≤ W' := fun y hy => hy.1

  have hAA' : A ≤ f ⁻¹ᵁ A' := by
    intro x hx
    have hxW : x ∈ W := hx.1
    have hfxW' : f.base x ∈ W' := hx.2
    refine ⟨hfxW', ?_⟩

    refine ⟨⟨f.base x, hWB hxW⟩, ?_, rfl⟩
    show gB.base ⟨f.base x, hWB hxW⟩ ∈ A
    have h1 : gB.base ((f.resLE B W hWB).base ⟨x, hxW⟩) = x := hb' ⟨x, hxW⟩
    have h2 : (f.resLE B W hWB).base ⟨x, hxW⟩ = ⟨f.base x, hWB hxW⟩ :=
      Subtype.ext (f.coe_resLE_apply hWB ⟨x, hxW⟩)
    rw [← h2, h1]
    exact hx

  have hrange : Set.range ((Y.homOfLE hA'B ≫ gB).base) ⊆ Set.range A.ι.base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨hyW', b, hb₀, hby⟩ := y.2
    have hb1 : (Y.homOfLE hA'B).base y = b := by
      apply B.ι.isOpenEmbedding.injective
      change (Y.homOfLE hA'B ≫ B.ι).base y = B.ι.base b
      rw [Scheme.homOfLE_ι]
      exact hby.symm
    rw [Scheme.Opens.range_ι]
    show gB.base ((Y.homOfLE hA'B).base y) ∈ A
    rw [hb1]
    exact hb₀
  let fA : (A : Scheme.{u}) ⟶ A' := f.resLE A' A hAA'
  let gA : (A' : Scheme.{u}) ⟶ A := IsOpenImmersion.lift A.ι (Y.homOfLE hA'B ≫ gB) hrange
  have hgA : gA ≫ A.ι = Y.homOfLE hA'B ≫ gB := IsOpenImmersion.lift_fac _ _ _
  have E1 : fA ≫ gA = 𝟙 _ := by
    rw [← cancel_mono A.ι, Category.assoc, hgA, Category.id_comp]
    change f.resLE A' A hAA' ≫ Y.homOfLE hA'B ≫ gB = A.ι
    rw [← Category.assoc, Scheme.Hom.resLE_map]
    have : f.resLE B A (hAA'.trans ((TopologicalSpace.Opens.map f.base).map hA'B.hom).le) =
        X.homOfLE (inf_le_left : A ≤ W) ≫ f.resLE B W hWB := by
      rw [Scheme.Hom.map_resLE]
    rw [this, Category.assoc, hb, Scheme.homOfLE_ι]
  have E2 : gA ≫ fA = 𝟙 _ := by
    rw [← cancel_mono A'.ι, Category.assoc, Category.id_comp]
    change gA ≫ f.resLE A' A hAA' ≫ A'.ι = A'.ι
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, hgA]
    rw [show Y.homOfLE hA'B = Y.homOfLE hA'W' ≫ Y.homOfLE hW'B from
      (Scheme.homOfLE_homOfLE Y hA'W' hW'B).symm]
    simp only [Category.assoc]
    rw [ha, Scheme.homOfLE_ι]
  haveI : IsIso fA := ⟨gA, E1, E2⟩
  have : A.ι ≫ f = fA ≫ A'.ι := (Scheme.Hom.resLE_comp_ι f hAA').symm
  rw [this]
  infer_instance

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι fromSpecStalk PartialMap fromSpecStalk_closedPoint Opens.range_ι Hom Hom.isoImage_inv_ι_assoc SpecMap_stalkSpecializes_fromSpecStalk Opens.fromSpecStalkOfMem Opens.fromSpecStalkOfMem_ι Hom.resLE_map functionField PartialMap.fromSpecStalkOfMem_ofFromSpecStalk PartialMap.mem_domain_ofFromSpecStalk homOfLE_homOfLE Hom.isoImage_inv_ι PartialMap.ofFromSpecStalk_comp Opens.fromSpecStalkOfMem_ι_assoc Hom.map_resLE SpecMap_stalkMap_fromSpecStalk Opens homOfLE_ι Opens.opensRange_ι Hom.comp_apply" namespace Opens p2m_export "AlgebraicGeometry.Scheme.Opens" "range_ι fromSpecStalkOfMem fromSpecStalkOfMem_ι fromSpecStalkOfMem_ι_assoc ι opensRange_ι" end Scheme.Opens
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.fromSpecStalk_comp_eq {X Y : Scheme.{u}} (U : X.Opens) {x : X} (hx : x ∈ U)
    {k₁ k₂ : (U : Scheme.{u}) ⟶ Y}
    (h : U.fromSpecStalkOfMem x hx ≫ k₁ = U.fromSpecStalkOfMem x hx ≫ k₂) :
    (U : Scheme.{u}).fromSpecStalk ⟨x, hx⟩ ≫ k₁ = (U : Scheme.{u}).fromSpecStalk ⟨x, hx⟩ ≫ k₂ := by
  simp only [Scheme.Opens.fromSpecStalkOfMem, Category.assoc] at h
  exact (cancel_epi _).mp h

theorem isOpenImmersion_ι_comp_of_inverse_on_opens' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Y.Opens) (gB : (B : Scheme.{u}) ⟶ X)
    (W₀ : (f ⁻¹ᵁ B : Scheme.{u}).Opens)
    (hb₀ : W₀.ι ≫ f.resLE B (f ⁻¹ᵁ B) le_rfl ≫ gB = W₀.ι ≫ (f ⁻¹ᵁ B).ι)
    (W'₀ : (B : Scheme.{u}).Opens) (ha₀ : W'₀.ι ≫ gB ≫ f = W'₀.ι ≫ B.ι) :
    IsOpenImmersion ((((f ⁻¹ᵁ B).ι ''ᵁ W₀) ⊓ f ⁻¹ᵁ (B.ι ''ᵁ W'₀)).ι ≫ f) := by
  set W : X.Opens := (f ⁻¹ᵁ B).ι ''ᵁ W₀
  set W' : Y.Opens := B.ι ''ᵁ W'₀
  have hWB : W ≤ f ⁻¹ᵁ B :=
    ((f ⁻¹ᵁ B).ι.image_le_opensRange W₀).trans (Scheme.Opens.opensRange_ι _).le
  have hW'B : W' ≤ B := (B.ι.image_le_opensRange W'₀).trans (Scheme.Opens.opensRange_ι _).le
  have hres : f.resLE B W hWB =
      ((f ⁻¹ᵁ B).ι.isoImage W₀).inv ≫ W₀.ι ≫ f.resLE B (f ⁻¹ᵁ B) le_rfl := by
    rw [← cancel_mono B.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.isoImage_inv_ι_assoc]
  have hb : f.resLE B W hWB ≫ gB = W.ι := by
    rw [hres]; simp only [Category.assoc]; rw [hb₀, Scheme.Hom.isoImage_inv_ι]
  have hhom : Y.homOfLE hW'B = (B.ι.isoImage W'₀).inv ≫ W'₀.ι := by
    rw [← cancel_mono B.ι, Scheme.homOfLE_ι, Category.assoc, Scheme.Hom.isoImage_inv_ι]
  have ha : Y.homOfLE hW'B ≫ gB ≫ f = W'.ι := by
    rw [hhom]; simp only [Category.assoc]; rw [ha₀, Scheme.Hom.isoImage_inv_ι]
  exact isOpenImmersion_ι_comp_of_inverse_on_opens f B gB W hWB hb W' hW'B ha

namespace Scheme.Opens
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

private theorem _root_.AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_eq_of_eq {X : Scheme.{u}} (U : X.Opens) {y y' : X}
    (e : y = y') (hy : y ∈ U) (hy' : y' ∈ U) :
    U.fromSpecStalkOfMem y hy =
      Spec.map (X.presheaf.stalkSpecializes (specializes_of_eq e)) ≫ U.fromSpecStalkOfMem y' hy' := by
  subst e; simp

end Scheme.Opens
p2m_export "AlgebraicGeometry" "Scheme.Opens.fromSpecStalkOfMem_eq_of_eq"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.fromSpecStalkOfMem_resLE {X Y : Scheme.{u}} (k : X ⟶ Y) (U : Y.Opens) (x : X)
    (hx : x ∈ k ⁻¹ᵁ U) :
    (k ⁻¹ᵁ U).fromSpecStalkOfMem x hx ≫ k.resLE U (k ⁻¹ᵁ U) le_rfl =
      Spec.map (k.stalkMap x) ≫ U.fromSpecStalkOfMem (k.base x) hx := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι_assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι fromSpecStalk PartialMap fromSpecStalk_closedPoint Opens.range_ι Hom Hom.isoImage_inv_ι_assoc SpecMap_stalkSpecializes_fromSpecStalk Opens.fromSpecStalkOfMem Opens.fromSpecStalkOfMem_ι Hom.resLE_map functionField PartialMap.fromSpecStalkOfMem_ofFromSpecStalk PartialMap.mem_domain_ofFromSpecStalk homOfLE_homOfLE Hom.isoImage_inv_ι PartialMap.ofFromSpecStalk_comp Opens.fromSpecStalkOfMem_ι_assoc Hom.map_resLE SpecMap_stalkMap_fromSpecStalk Opens homOfLE_ι Opens.opensRange_ι Hom.comp_apply" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.b1_main
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsIntegral C'] [LocallyOfFiniteType c] [LocallyOfFiniteType c']
    (ψ : C.functionField ≅ C'.functionField)
    (hψ : Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') ≫ c' =
      C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ (U : C.Opens) (hη : genericPoint C ∈ U) (j : (U : Scheme.{u}) ⟶ C') (_ : IsOpenImmersion j),
      j ≫ c' = U.ι ≫ c ∧
      U.fromSpecStalkOfMem (genericPoint C) hη ≫ j =
        Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') := by
  classical

  let φ₁ : Spec (C.presheaf.stalk (genericPoint C)) ⟶ C' :=
    Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C')
  have h₁ : φ₁ ≫ c' = C.fromSpecStalk (genericPoint C) ≫ c := by
    simpa only [φ₁, Category.assoc] using hψ
  obtain ⟨D, hηD, fh, hf₁, hf₂⟩ : ∃ (D : C.Opens) (hηD : genericPoint C ∈ D) (fh : (D : Scheme.{u}) ⟶ C'),
      D.fromSpecStalkOfMem (genericPoint C) hηD ≫ fh = φ₁ ∧ fh ≫ c' = D.ι ≫ c :=
    ⟨_, Scheme.PartialMap.mem_domain_ofFromSpecStalk c c' φ₁ h₁, _,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk c c' φ₁ h₁,
      Scheme.PartialMap.ofFromSpecStalk_comp c c' φ₁ h₁⟩
  haveI : Nonempty D := ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))⟩
  haveI hIsoSM : IsIso (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))) := inferInstance

  haveI : IsLocalHom ψ.inv.hom := isLocalHom_of_isIso ψ.inv
  have hDpt : (D.fromSpecStalkOfMem (genericPoint C) hηD)
      (IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))) = (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) := by
    apply D.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
    rfl
  have hfη : fh (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) = genericPoint C' := by
    have := congrArg (fun k => k (IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C)))) hf₁
    simp only [Scheme.Hom.comp_apply, hDpt] at this
    rw [this]
    simp only [φ₁, Scheme.Hom.comp_apply]
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

  let φ₂ : Spec (C'.presheaf.stalk (genericPoint C')) ⟶ (D : Scheme.{u}) :=
    Spec.map ψ.hom ≫ D.fromSpecStalkOfMem (genericPoint C) hηD
  have h₂ : φ₂ ≫ (D.ι ≫ c) = C'.fromSpecStalk (genericPoint C') ≫ c' := by
    simp only [φ₂, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
    rw [← hψ, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  obtain ⟨B, hη'B, gB, hg₁⟩ : ∃ (B : C'.Opens) (hη'B : genericPoint C' ∈ B)
      (gB : (B : Scheme.{u}) ⟶ D), B.fromSpecStalkOfMem (genericPoint C') hη'B ≫ gB = φ₂ :=
    ⟨_, Scheme.PartialMap.mem_domain_ofFromSpecStalk c' (D.ι ≫ c) φ₂ h₂, _,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk c' (D.ι ≫ c) φ₂ h₂⟩
  haveI : Nonempty B := ⟨⟨genericPoint C', hη'B⟩⟩

  have key_a : B.fromSpecStalkOfMem (genericPoint C') hη'B ≫ gB ≫ fh =
      B.fromSpecStalkOfMem (genericPoint C') hη'B ≫ B.ι := by
    rw [← Category.assoc, hg₁, Scheme.Opens.fromSpecStalkOfMem_ι]
    simp only [φ₂, Category.assoc]
    rw [hf₁]
    simp only [φ₁]
    rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  obtain ⟨W'₀, hW'₀, ha₀⟩ := spread_out_unique_of_isGermInjective' (X := (B : Scheme.{u}))
    (x := ⟨genericPoint C', hη'B⟩) (gB ≫ fh) B.ι (Scheme.Opens.fromSpecStalk_comp_eq B hη'B key_a)

  have hηfB : (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ fh ⁻¹ᵁ B := by
    show fh (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ B
    rw [hfη]; exact hη'B
  have key_b : Scheme.Opens.fromSpecStalkOfMem (fh ⁻¹ᵁ B) (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) hηfB ≫ fh.resLE B (fh ⁻¹ᵁ B) le_rfl ≫ gB =
      Scheme.Opens.fromSpecStalkOfMem (fh ⁻¹ᵁ B) (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) hηfB ≫ (fh ⁻¹ᵁ B).ι := by
    rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_resLE, Category.assoc,
      B.fromSpecStalkOfMem_eq_of_eq hfη hηfB hη'B, Category.assoc, hg₁]
    simp only [φ₂]
    rw [Scheme.Opens.fromSpecStalkOfMem_ι]
    have hD : (D : Scheme.{u}).fromSpecStalk (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) =
        Spec.map (D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))) ≫ D.fromSpecStalkOfMem (genericPoint C) hηD := by
      simp [Scheme.Opens.fromSpecStalkOfMem]
    rw [hD]
    simp only [← Spec.map_comp_assoc]
    congr 2

    have hf₁' := hf₁
    rw [Scheme.Opens.fromSpecStalkOfMem] at hf₁'
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk fh (x := (⟨genericPoint C, hηD⟩ : (D : Scheme.{u}))),
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq hfη)] at hf₁'
    simp only [φ₁, ← Spec.map_comp_assoc] at hf₁'
    have hinj := Spec.map_injective ((cancel_mono (C'.fromSpecStalk (genericPoint C'))).mp hf₁')

    have hinj' : C'.presheaf.stalkSpecializes (specializes_of_eq hfη) ≫ fh.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) =
        ψ.inv ≫ D.ι.stalkMap (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) :=
      (@IsIso.comp_inv_eq _ _ _ _ _ _ hIsoSM _ _).mp (by simp only [Category.assoc] at hinj; exact hinj)
    rw [Category.assoc, hinj', Iso.hom_inv_id_assoc]
  haveI : Nonempty (fh ⁻¹ᵁ B) := ⟨⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩⟩
  obtain ⟨W₀, hW₀, hb₀⟩ := spread_out_unique_of_isGermInjective' (X := ((fh ⁻¹ᵁ B : (D : Scheme.{u}).Opens) : Scheme.{u}))
    (x := ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩) (fh.resLE B (fh ⁻¹ᵁ B) le_rfl ≫ gB) (fh ⁻¹ᵁ B).ι
    (Scheme.Opens.fromSpecStalk_comp_eq (fh ⁻¹ᵁ B) hηfB key_b)

  have hOI := isOpenImmersion_ι_comp_of_inverse_on_opens' fh B gB W₀ hb₀ W'₀ ha₀
  set A : (D : Scheme.{u}).Opens := ((fh ⁻¹ᵁ B).ι ''ᵁ W₀) ⊓ fh ⁻¹ᵁ (B.ι ''ᵁ W'₀) with hAdef
  have hηA : (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ A := by
    refine ⟨⟨⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηfB⟩, hW₀, rfl⟩, ?_⟩
    show fh (⟨genericPoint C, hηD⟩ : (D : Scheme.{u})) ∈ B.ι ''ᵁ W'₀
    exact ⟨⟨genericPoint C', hη'B⟩, hW'₀, hfη.symm⟩

  refine ⟨D.ι ''ᵁ A, ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηA, rfl⟩, (D.ι.isoImage A).inv ≫ A.ι ≫ fh, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hf₂, Scheme.Hom.isoImage_inv_ι_assoc]
  · have hlift : (D.ι ''ᵁ A).fromSpecStalkOfMem (genericPoint C) ⟨(⟨genericPoint C, hηD⟩ : (D : Scheme.{u})), hηA, rfl⟩ ≫
        (D.ι.isoImage A).inv ≫ A.ι = D.fromSpecStalkOfMem (genericPoint C) hηD := by
      rw [← cancel_mono D.ι]
      simp only [Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [← Category.assoc, ← Category.assoc, Category.assoc _ (D.ι.isoImage A).inv, hlift, hf₁]

end AlgebraicGeometry

theorem solution
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsIntegral C'] [LocallyOfFiniteType c] [LocallyOfFiniteType c']
    (ψ : C.functionField ≅ C'.functionField)
    (hψ : Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') ≫ c' =
      C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ (U : C.Opens) (hη : genericPoint C ∈ U) (j : (U : Scheme.{u}) ⟶ C') (_ : IsOpenImmersion j),
      j ≫ c' = U.ι ≫ c ∧
      U.fromSpecStalkOfMem (genericPoint C) hη ≫ j =
        Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') :=
  AlgebraicGeometry.Scheme.b1_main c c' ψ hψ

end S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso (solution)
