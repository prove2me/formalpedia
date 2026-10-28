-- Prove2me | solution 1 for AlgebraicGeometry.hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T21:43:33.319084+00:00
-- url     : https://prove2.me/submissions/695f24aa-dbf5-49e0-ac5b-7f4afe95b885

import Definitions.Def_PhilipponMultiplicity_GenericCurveCoverFamily
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_finite_extension_smooth_projective_cover_of_scalarExtension_of_proper_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_model_of_finite_genericResidueField_extension
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_generic_cover_family_of_noetherian_fractionField

universe u
noncomputable section
set_option linter.style.haveILetI false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericFieldBaseChange

/-- Two base-change paths with the same composite retain canonically
isomorphic actual fibres, with both original projections fixed. -/
lemma exists_comparison_iso
    {X S T U V : Scheme.{u}} (q : X ⟶ S) (a : T ⟶ S) (b : U ⟶ S)
    (c : V ⟶ T) (d : V ⟶ U) (h : c ≫ a = d ≫ b) :
    ∃ e : pullback (pullback.snd q a) c ≅ pullback (pullback.snd q b) d,
      e.hom ≫ pullback.snd (pullback.snd q b) d = pullback.snd (pullback.snd q a) c ∧
      e.hom ≫ pullback.fst (pullback.snd q b) d ≫ pullback.fst q b =
        pullback.fst (pullback.snd q a) c ≫ pullback.fst q a := by
  let hp₁ := (IsPullback.of_hasPullback (pullback.snd q a) c).paste_horiz
    (IsPullback.of_hasPullback q a)
  have hp₂ : IsPullback
      (pullback.fst (pullback.snd q b) d ≫ pullback.fst q b)
      (pullback.snd (pullback.snd q b) d) q (c ≫ a) := by
    rw [h]
    exact (IsPullback.of_hasPullback (pullback.snd q b) d).paste_horiz
      (IsPullback.of_hasPullback q b)
  let e := hp₁.isoPullback ≪≫ hp₂.isoPullback.symm
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, hp₂.isoPullback_inv_snd, hp₁.isoPullback_hom_snd]
  · dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, hp₂.isoPullback_inv_fst, hp₁.isoPullback_hom_fst]

end PhilipponGenericFieldBaseChange

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponGenericDominance

lemma genericPoint_eq_of_dominant
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] : q (genericPoint X) = genericPoint S := by
  have h := (genericPoint_spec X).image q.continuous
  have hg : IsGenericPoint (q (genericPoint X)) (Set.univ : Set S) := by
    simpa only [Set.image_univ, q.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec S)

lemma genericFiber_inclusion
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] (η : S) (hη : IsGenericPoint η Set.univ) :
    IsDominant (q.fiberι η) := by
  have hηeq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (q.fiberι (genericPoint S)) := by
    refine ⟨(q.fiberHomeo (genericPoint S)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant q⟩, ?_⟩
    exact q.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (q.fiberι (genericPoint S)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma of_recovered_generic_cover
    {C F Y X : Scheme.{u}} (e : C ⟶ Y) (f : Y ⟶ X) (a : C ⟶ F) (i : F ⟶ X)
    [Surjective a] [IsDominant i] (h : e ≫ f = a ≫ i) : IsDominant f := by
  haveI : IsDominant (e ≫ f) := by rw [h]; infer_instance
  exact IsDominant.of_comp e f

end PhilipponGenericDominance

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PhilipponNoetherianPresentation

lemma locallyOfFinitePresentation_of_locallyOfFiniteType
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV hVU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact RingHom.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hVU)

end PhilipponNoetherianPresentation

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponFiniteBaseFamily

/-- The actual generic curve supplies a smooth projective covering family
on an open of a normal projective finite-field base model. -/
theorem exists_normal_projective_base_and_cover_family
    (k : Type u) [Field k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (q : X ⟶ S) [IsProper q] [IsDominant q]
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∃ E : IntermediateField (S.residueField η) (AlgebraicClosure (S.residueField η)),
      FiniteDimensional (S.residueField η) E ∧
      letI : Algebra k E := ((algebraMap (S.residueField η) E).comp (algebraMap k (S.residueField η))).toAlgebra
      ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧ IsFractionRing B E ∧
        ∃ (N : Scheme.{u}) (qN : N ⟶ S) (t : Spec (.of B) ⟶ N),
          IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
          IsProper qN ∧ Surjective qN ∧ IsOpenImmersion t ∧ IsDominant t ∧
          topologicalKrullDim N = topologicalKrullDim S ∧
          t ≫ (qN ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
          Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ qN =
            Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫ S.fromSpecResidueField η ∧
          (∃ (nN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nN + 1)) k)),
            IsClosedImmersion iN ∧ iN ≫ ProjSpace.π k nN = qN ≫ π) ∧
          ∃ a : B, a ≠ 0 ∧ ∃ (nM : ℕ) (M : Scheme.{u})
            (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) (Localization.Away a))),
            IsClosedImmersion iM ∧
            ∃ (U : Scheme.{u}) (j : U ⟶ Spec (.of (Localization.Away a))),
              IsOpenImmersion j ∧ DenseRange j ∧
              let u : U ⟶ N := (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ≫ t
              IsOpenImmersion u ∧ IsDominant u ∧
              ∃ (Y Z : Scheme.{u}) (pY : Y ⟶ U) (pZ : Z ⟶ U)
                (tY : Y ⟶ M) (tZ : Z ⟶ X) (h : Y ⟶ Z),
                IsPullback tY pY (iM ≫ ProjSpace.π (Localization.Away a) nM) j ∧
                IsPullback tZ pZ q (u ≫ qN) ∧ Flat pZ ∧ IsProper pZ ∧
                h ≫ pZ = pY ∧ IsProper h ∧ Surjective h ∧
                Smooth pY ∧ IsProper pY ∧ IsDominant (h ≫ tZ) ∧
                ∃ (C₀ : Scheme.{u}) (p₀ : C₀ ⟶ Spec (.of E)) (a₀ : C₀ ⟶ q.fiber η),
                  Smooth p₀ ∧ IsProper p₀ ∧ topologicalKrullDim C₀ ≤ 1 ∧
                  IsProper a₀ ∧ Surjective a₀ ∧
                  a₀ ≫ q.fiberToSpecResidueField η = p₀ ≫
                    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ∧
                  (∃ i₀ : C₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) E),
                    IsClosedImmersion i₀ ∧ i₀ ≫ ProjSpace.π E nM = p₀) ∧
                  ∃ (b : Spec (.of E) ⟶ U) (eC : C₀ ⟶ Y),
                    b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ∧
                    IsPullback eC p₀ pY b ∧ eC ≫ h ≫ tZ = a₀ ≫ q.fiberι η := by
  let κ := S.residueField η
  letI : Algebra k κ :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
  let πC := q.fiberToSpecResidueField η
  haveI : IsProper πC := MorphismProperty.pullback_snd q (S.fromSpecResidueField η) inferInstance
  obtain ⟨E, hE, C₀, a₀, p₀, hpa₀, hsa₀, hsm₀, hpp₀, hdC₀, hbase₀,
    n₀, i₀, hi₀, hpi₀, α, hαf, hαp, _hαproper, hαsurj⟩ :=
    AlgebraicGeometry.exists_finite_extension_smooth_projective_cover_of_scalarExtension_of_proper_dimension_le_one
      κ (AlgebraicClosure κ) πC hdim
  haveI : FiniteDimensional κ E := hE
  letI : Algebra k E := ((algebraMap κ E).comp (algebraMap k κ)).toAlgebra
  letI : IsScalarTower k κ E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B, hBft, hBn, hBE, N, qN, t, hN, hnN, hqN, hsqN, ht, htd, hdN,
    htbase, hgeneric, nN, iN, hiN, hbaseN⟩ :=
    AlgebraicGeometry.exists_normal_projective_model_of_finite_genericResidueField_extension
      k π m i hi η hη E
  haveI : Algebra.FiniteType k B := hBft
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsFractionRing B E := hBE
  haveI : IsIntegral N := hN
  haveI : IsOpenImmersion t := ht
  let β := t ≫ qN
  let bBE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bκE := Spec.map (CommRingCat.ofHom (algebraMap κ E))
  have hβ : bBE ≫ β = bκE ≫ S.fromSpecResidueField η := hgeneric
  let fB := pullback.snd q β
  haveI : LocallyOfFinitePresentation fB :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType fB
  obtain ⟨e, heS, heX⟩ := PhilipponGenericFieldBaseChange.exists_comparison_iso
    q (S.fromSpecResidueField η) β bκE bBE hβ.symm
  let e' : pullback πC bκE ≅ pullback fB bBE := e
  have heS' : e'.hom ≫ pullback.snd fB bBE = pullback.snd πC bκE := heS
  have heX' : e'.hom ≫ pullback.fst fB bBE ≫ pullback.fst q β =
      pullback.fst πC bκE ≫ q.fiberι η := heX
  let g := α ≫ e'.hom
  haveI : Surjective α := hαsurj
  haveI : IsClosedImmersion i₀ := hi₀
  haveI : Smooth (i₀ ≫ ProjSpace.π E n₀) := by rw [hpi₀]; exact hsm₀
  have hg : g ≫ pullback.snd fB bBE = i₀ ≫ ProjSpace.π E n₀ := by
    dsimp only [g]
    rw [Category.assoc, heS', hαp, hpi₀]
  have hsurG : Surjective (α ≫ e'.hom) := inferInstance
  have hgs : Function.Surjective g := hsurG.1
  obtain ⟨a, ha, γ, _hγ, M, iM, _gM, hiM, _hpM,
    U, j, hj, hdj, Y, Z, pY, pZ, tY, tB, hpY, hpZ, hsmY, hprY, hflZ, hprZ,
    h, hover, hproper, hsurj, b, eC, eX, hb, heC, _heX, _heCt, heXt, hrec⟩ :=
    AlgebraicGeometry.exists_smooth_projective_generic_cover_family_of_noetherian_fractionField
      B E fB C₀ n₀ i₀ g hg hgs
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))
  let u := (j ≫ bA) ≫ t
  let tZ := tB ≫ pullback.fst q β
  haveI : IsOpenImmersion j := hj
  haveI : IsOpenImmersion bA := IsOpenImmersion.of_isLocalization a
  haveI : IsOpenImmersion u := by dsimp only [u]; infer_instance
  have hne : Nonempty U := ⟨b default⟩
  letI := hne
  have hu : IsDominant u := ⟨u.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hpZ' : IsPullback tZ pZ q (u ≫ qN) := by
    simpa only [tZ, u, β, Category.assoc] using
      hpZ.paste_horiz (IsPullback.of_hasPullback q β)
  have hγbase : Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ bA = bBE := by
    dsimp only [bA, bBE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  have hbu : b ≫ u = bBE ≫ t := by
    dsimp only [u]
    calc
      b ≫ ((j ≫ bA) ≫ t) = ((b ≫ j) ≫ bA) ≫ t := by simp only [Category.assoc]
      _ = bBE ≫ t := by rw [hb, hγbase]
  have hrecover : eC ≫ h ≫ tZ = a₀ ≫ q.fiberι η := by
    calc
      eC ≫ h ≫ tZ = g ≫ eX ≫ tZ := by rw [← Category.assoc, hrec, Category.assoc]
      _ = g ≫ pullback.fst fB bBE ≫ pullback.fst q β := by
        dsimp only [tZ]
        rw [← Category.assoc eX, heXt]
      _ = α ≫ (e'.hom ≫ pullback.fst fB bBE ≫ pullback.fst q β) := by
        dsimp only [g]; simp only [Category.assoc]
      _ = α ≫ (pullback.fst πC bκE ≫ q.fiberι η) := by rw [heX']
      _ = a₀ ≫ q.fiberι η := by rw [← Category.assoc, hαf]
  haveI : Surjective a₀ := hsa₀
  haveI : IsDominant (q.fiberι η) := PhilipponGenericDominance.genericFiber_inclusion q η hη
  have hdom : IsDominant (h ≫ tZ) :=
    PhilipponGenericDominance.of_recovered_generic_cover eC (h ≫ tZ) a₀ (q.fiberι η) hrecover
  have heC' : IsPullback eC p₀ pY b := by simpa only [hpi₀] using heC
  exact ⟨E, hE, B, hBft, hBn, hBE, N, qN, t, hN, hnN, hqN, hsqN, ht, htd, hdN,
    htbase, hgeneric, ⟨nN, iN, hiN, hbaseN⟩, a, ha, n₀, M, iM, hiM,
    U, j, hj, hdj, inferInstance, hu, Y, Z, pY, pZ, tY, tZ, h,
    hpY, hpZ', hflZ, hprZ, hover, hproper, ⟨hsurj⟩, hsmY, hprY, hdom,
    C₀, p₀, a₀, hsm₀, hpp₀, hdC₀, hpa₀, hsa₀, hbase₀, ⟨i₀, hi₀, hpi₀⟩,
    b, eC, hbu, heC', hrecover⟩

end PhilipponFiniteBaseFamily

theorem solution
    (k : Type u) [Field k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (q : X ⟶ S) [IsProper q] [IsDominant q]
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    AlgebraicGeometry.HasNormalProjectiveBaseSmoothCurveCoverFamily k π q η := by
  exact PhilipponFiniteBaseFamily.exists_normal_projective_base_and_cover_family k π m i hi q η hη hdim
