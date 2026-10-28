-- Prove2me | solution 1 for AlgebraicGeometry.exists_finite_extension_integral_smooth_projective_cover_of_integral_proper_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T02:00:03.157968+00:00
-- url     : https://prove2.me/submissions/a58e2a4b-df4d-443f-9a6b-664f28b76e16

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isPullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

universe u
set_option linter.style.haveILetI false




set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProperCurveMap

lemma closed_of_ne_generic {X : Type*} [TopologicalSpace X] [T0Space X]
    [QuasiSober X] [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  let Z : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin Z := by
    rcases Order.krullDim_le_one_iff.mp hdim Z with h | h
    · exact h
    · have heq : Z = T := le_antisymm (fun _ _ => trivial) (h (fun _ _ => trivial))
      apply False.elim
      apply hx
      apply (isGenericPoint_closure (x := x)).eq
      rw [show closure {x} = Set.univ from congrArg
        (fun a : TopologicalSpace.IrreducibleCloseds X => (a : Set X)) heq]
      exact genericPoint_spec X
  have hcl : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm ?_ subset_closure
    intro y hy
    let Y : TopologicalSpace.IrreducibleCloseds X :=
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hYZ : Y ≤ Z := closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure
    have hZY : Z ≤ Y := hmin hYZ
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    have hyx : y ⤳ x := specializes_iff_mem_closure.mpr
      (hZY (subset_closure (Set.mem_singleton x)))
    exact Set.mem_singleton_iff.mpr ((hxy.antisymm hyx).eq.symm)
  exact closure_eq_iff_isClosed.mp hcl

end PhilipponProperCurveMap

namespace PhilipponIntegralMultisection

lemma reduced_vanishing_subscheme {X : Scheme.{u}} (S : TopologicalSpace.Closeds X) :
    AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hred (U : X.affineOpens) : AlgebraicGeometry.IsReduced
      (Spec (.of (Γ(X, U) ⧸ I.ideal U))) := by
    have hrad : (I.ideal U).IsRadical := by
      change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (S : Set X))).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hrad
    infer_instance
  letI (U : I.subschemeCover.openCover.I₀) :
      AlgebraicGeometry.IsReduced (I.subschemeCover.openCover.X U) := hred U
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

lemma integral_reduced_closure {X : Scheme.{u}} (x : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({x} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme := by
  let S : TopologicalSpace.Closeds X := ⟨closure {x}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have : AlgebraicGeometry.IsReduced I.subscheme := reduced_vanishing_subscheme S
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    have hsupport : (I.support : Set X) = closure ({x} : Set X) := by
      simp [I, S]
    rw [hsupport]
    exact Subtype.irreducibleSpace isIrreducible_singleton.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

abbrev residueAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma preimage_residue_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  apply ext_of_isAffine
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  have ht : (Spec.map (Scheme.ΓSpecIso (.of K)).inv).appTop =
      (Scheme.ΓSpecIso Γ(Spec (.of K), ⊤)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
    exact (Scheme.ΓSpecIso_inv_naturality (Scheme.ΓSpecIso (.of K)).inv).symm
  simp
  simp only [Scheme.Hom.appTop] at ht ⊢
  rw [ht]

lemma finite_residue_of_closed {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := residueAlgebra f x
    Module.Finite K (X.residueField x) := by
  letI := residueAlgebra f x
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have h := (IsFinite.SpecMap_iff
    (Spec.preimage (X.fromSpecResidueField x ≫ f))).mp
      (show IsFinite (Spec.map (Spec.preimage (X.fromSpecResidueField x ≫ f))) by
        simpa using (inferInstance : IsFinite (X.fromSpecResidueField x ≫ f)))
  rw [preimage_residue_comp] at h
  exact h

lemma residue_tower {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X) :
    letI := residueAlgebra g (f x)
    letI := residueAlgebra (f ≫ g) x
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  letI := residueAlgebra g (f x)
  letI := residueAlgebra (f ≫ g) x
  letI := (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := congrArg Spec.preimage
    (congrArg (fun a => a ≫ g)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map,
    preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma residue_base_tower {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of F)) (x : X) :
    letI := residueAlgebra s x
    letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
    IsScalarTower K F (X.residueField x) := by
  letI := residueAlgebra s x
  letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := Spec.preimage_comp (X.fromSpecResidueField x ≫ s)
    (Spec.map (CommRingCat.ofHom (algebraMap K F)))
  rw [Spec.preimage_map] at h
  simp only [Category.assoc, preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h

lemma generic_trdeg_le_one {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [LocallyOfFiniteType c]
    (hdim : topologicalKrullDim C ≤ 1) :
    letI := residueAlgebra c (genericPoint C)
    Algebra.trdeg K (C.residueField (genericPoint C)) ≤ 1 := by
  letI := residueAlgebra c (genericPoint C)
  have h := toENat_trdeg_residueField_eq_topologicalKrullDim_closure c (genericPoint C)
  have h' : Cardinal.toENat (Algebra.trdeg K (C.residueField (genericPoint C))) ≤ 1 := by
    exact_mod_cast h.le.trans ((topologicalKrullDim_subspace_le C _).trans hdim)
  exact Cardinal.toENat_le_one.mp h'

lemma dimension_closure_of_closed_generic_fiber {K : Type u} [Field K]
    {C Z : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [LocallyOfFiniteType c] (hdim : topologicalKrullDim C ≤ 1)
    (p : Z ⟶ C) [LocallyOfFiniteType p]
    (q : p.fiber (genericPoint C))
    (hq : IsClosed ({q} : Set (p.fiber (genericPoint C)))) :
    topologicalKrullDim (closure ({p.fiberι (genericPoint C) q} : Set Z)) ≤ 1 := by
  let η := genericPoint C
  let F := C.residueField η
  let Y := p.fiber η
  let s : Y ⟶ Spec F := p.fiberToSpecResidueField η
  let t : Y ⟶ Z := p.fiberι η
  let E := Y.residueField q
  let z := t q
  let L := Z.residueField z
  letI : Algebra K F := residueAlgebra c η
  letI : Algebra F E := residueAlgebra s q
  letI : Algebra K E := residueAlgebra (t ≫ (p ≫ c)) q
  letI : Algebra K L := residueAlgebra (p ≫ c) z
  letI : Algebra L E := (t.residueFieldMap q).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower t (p ≫ c) q
  have hbase : t ≫ (p ≫ c) = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    change p.fiberι η ≫ (p ≫ c) =
      p.fiberToSpecResidueField η ≫ Spec.map
        ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop ≫
          C.presheaf.germ ⊤ η trivial ≫ C.residue η)
    rw [← preimage_residue_comp, Spec.map_preimage, ← Category.assoc, p.fiber_fac]
    exact Category.assoc _ _ _
  letI : IsScalarTower K F E := by
    have h := residue_base_tower (K := K) (F := F) s q
    rw [← hbase] at h
    exact h
  letI : LocallyOfFiniteType s := inferInstanceAs (LocallyOfFiniteType (pullback.snd p _))
  letI : Module.Finite F E := finite_residue_of_closed s q hq
  have hF : Algebra.trdeg K F ≤ 1 := generic_trdeg_le_one c hdim
  have hE : Algebra.trdeg K E ≤ 1 := by
    rw [← trdeg_add_eq K F (A := E),
      show Algebra.trdeg F E = 0 from trdeg_eq_zero, add_zero]
    exact hF
  have hL : Algebra.trdeg K L ≤ 1 := by
    apply le_trans ?_ hE
    rw [← trdeg_add_eq K L (A := E)]
    exact le_self_add
  have h := toENat_trdeg_residueField_eq_topologicalKrullDim_closure (p ≫ c) z
  rw [← h]
  exact_mod_cast (Cardinal.toENat_le_one.mpr hL)

lemma finite_of_dimension_le_one {K : Type u} [Field K] {D Y : Scheme.{u}}
    (d : D ⟶ Spec (.of K)) [IsIntegral D] [IsProper d]
    (hdim : topologicalKrullDim D ≤ 1) (y : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType y] [IsSeparated y]
    (f : D ⟶ Y) (hf : f ≫ y = d) (hn : ¬ (Set.range f).Subsingleton) : IsFinite f := by
  let : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian d
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace d
  let : AlgebraicGeometry.IsNoetherian D := ⟨⟩
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace y
  have : IsProper (f ≫ y) := by rw [hf]; infer_instance
  have : IsProper f := IsProper.of_comp f y
  have hD := PhilipponProperCurveMap.closed_of_ne_generic hdim
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro z
  obtain ⟨v, hvz, hv⟩ := nonempty_inter_closedPoints
    (Set.singleton_nonempty z |>.mono subset_closure) isClosed_closure.isLocallyClosed
  have hzv : z ⤳ v := specializes_iff_mem_closure.mpr hvz
  have hpre : IsClosed (f ⁻¹' {v}) := hv.preimage f.continuous
  have hne : f ⁻¹' {v} ≠ Set.univ := by
    intro heq
    apply hn
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have ha : f a = v := by
      have : a ∈ f ⁻¹' {v} := heq.symm ▸ Set.mem_univ a
      exact this
    have hb : f b = v := by
      have : b ∈ f ⁻¹' {v} := heq.symm ▸ Set.mem_univ b
      exact this
    exact ha.trans hb.symm
  have hfin := Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton hD
    (f ⁻¹' {v}) hpre hne
  obtain ⟨V, hvV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f v hfin
  exact ⟨V, hzv.mem_open V.isOpen hvV, hV⟩

lemma not_subsingleton_smooth_curve
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [SmoothOfRelativeDimension 1 c] :
    ¬ Subsingleton C := by
  intro h
  let := h
  have hx : IsClosed ({genericPoint C} : Set C) := by
    have : ({genericPoint C} : Set C) = Set.univ :=
      Set.eq_univ_iff_forall.mpr (fun x => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))
    rw [this]
    exact isClosed_univ
  have hdim := SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed K c 1
    (genericPoint C) hx
  have hzero : ringKrullDim (C.presheaf.stalk (genericPoint C)) = 0 :=
    ringKrullDim_eq_zero_of_field C.functionField
  exact zero_ne_one (hzero.symm.trans hdim)

end PhilipponIntegralMultisection


namespace PhilipponCurveProjectivity

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h


lemma dimension_le_one_of_open_immersion {K : Type u} [Field K]
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (f : U ⟶ W) [IsOpenImmersion f]
    (d : W ⟶ Spec (.of K)) [LocallyOfFiniteType d]
    (hdim : topologicalKrullDim U ≤ 1) : topologicalKrullDim W ≤ 1 := by
  let u := genericPoint U
  let L := W.residueField (f u)
  let E := U.residueField u
  letI : Algebra K L := PhilipponIntegralMultisection.residueAlgebra d (f u)
  letI : Algebra K E := PhilipponIntegralMultisection.residueAlgebra (f ≫ d) u
  letI : Algebra L E := (f.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := PhilipponIntegralMultisection.residue_tower f d u
  letI : IsIso (f.residueFieldMap u) :=
    isIso_residueFieldMap_of_isPreimmersion f u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  have hW := toENat_trdeg_residueField_eq_topologicalKrullDim_closure d (f u)
  have hU := toENat_trdeg_residueField_eq_topologicalKrullDim_closure (f ≫ d) u
  have hgen : f u = genericPoint W := genericPoint_eq_of_isOpenImmersion f
  have hcl : closure ({f u} : Set W) = Set.univ := by rw [hgen]; exact genericPoint_spec W
  have hd : topologicalKrullDim W = topologicalKrullDim (closure ({f u} : Set W)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ W)
      (Homeomorph.Set.univ W).isHomeomorph).symm
  rw [hd, ← hW]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) ≤ 1
  rw [he]
  change (Cardinal.toENat (Algebra.trdeg K (U.residueField u)) : WithBot ℕ∞) ≤ 1
  rw [hU]
  exact (topologicalKrullDim_subspace_le U _).trans hdim

theorem exists_projective_embedding_of_smooth_proper_curve
    (K : Type u) [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    ∃ (n : ℕ) (i : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
      IsClosedImmersion i ∧ i ≫ ProjSpace.π K n = c := by
  classical
  letI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  letI : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  obtain ⟨D⟩ := ChowDatumProj.nonempty_of c (ChowDatum.nonempty c)
  let V := D.U
  letI : Nonempty (V : Scheme) := by
    obtain ⟨x, hx⟩ := D.hU_dense.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI : IsIntegral (V : Scheme) := isIntegral_of_isOpenImmersion V.ι
  let s₀ : (V : Scheme) ⟶ D.V' :=
    inv (pullback.snd D.p V.ι) ≫ pullback.fst D.p V.ι
  letI : IsOpenImmersion s₀ := inferInstance
  letI : QuasiCompact s₀ := inferInstance
  obtain ⟨hW, _, _⟩ := s₀.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
  letI := hW
  let W := s₀.image
  let g : W ⟶ C := s₀.imageι ≫ D.p
  let s : (V : Scheme) ⟶ W := s₀.toImage
  have hsg : s ≫ g = V.ι := by
    simp only [s, g, ← Category.assoc, Scheme.Hom.toImage_imageι]
    dsimp [s₀]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  have hsurj : Surjective g := by
    constructor
    have hc : IsClosed (Set.range g) := by
      simpa only [Set.image_univ] using g.isClosedMap _ isClosed_univ
    have hV : (V : Set C) ⊆ Set.range g := by
      intro x hx
      refine ⟨s ⟨x, hx⟩, ?_⟩
      have h := congrArg (fun f : (V : Scheme) ⟶ C => f ⟨x, hx⟩) hsg
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h
    have hall : Set.univ ⊆ Set.range g := by
      rw [← D.hU_dense.closure_eq]
      exact closure_minimal hV hc
    exact fun x => hall (Set.mem_univ x)
  letI := hsurj
  have hdimV : topologicalKrullDim (V : Scheme) ≤ 1 :=
    V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
      (SmoothOfRelativeDimension.topologicalKrullDim_le c 1)
  have hdimW : topologicalKrullDim W ≤ 1 :=
    dimension_le_one_of_open_immersion s (g ≫ c) hdimV
  have hn : ¬ (Set.range g).Subsingleton := by
    intro hs
    apply PhilipponIntegralMultisection.not_subsingleton_smooth_curve c
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := g.surjective x
    obtain ⟨b, rfl⟩ := g.surjective y
    exact hs (Set.mem_range_self a) (Set.mem_range_self b)
  letI : IsFinite g := PhilipponIntegralMultisection.finite_of_dimension_le_one
    (g ≫ c) hdimW c g rfl hn
  letI : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have hnormal : ∀ x : C,
      IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x) :=
    Smooth.isDomain_and_isIntegrallyClosed_stalk c
  letI : IsOpenImmersion g :=
    isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
      g hnormal V D.hU_dense s hsg s.denseRange
  letI : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr
    ⟨inferInstance, inferInstance⟩
  let i := inv g ≫ (s₀.imageι ≫ D.ιN)
  refine ⟨D.Nd, i, inferInstance, ?_⟩
  change (inv g ≫ (s₀.imageι ≫ D.ιN)) ≫ ProjSpace.π K D.Nd = c
  rw [Category.assoc, Category.assoc, D.hoverN, ← Category.assoc s₀.imageι]
  change inv g ≫ g ≫ c = c
  simp

end PhilipponCurveProjectivity

namespace PhilipponAlterationBaseCases

lemma isIso_of_integral_subsingleton_over_algClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    [IsIntegral X] [Subsingleton X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    IsIso π := by
  letI : IsFinite π := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let f : Spec Γ(X, ⊤) ⟶ Spec (.of K) := X.isoSpec.inv ≫ π
  let r := Spec.preimage f
  have hfinite : r.hom.Finite := (IsFinite.SpecMap_iff r).mp (by
    rw [Spec.map_preimage]
    infer_instance)
  letI := r.hom.toAlgebra
  letI : Module.Finite K Γ(X, ⊤) := hfinite
  have hbij : Function.Bijective r :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
  letI : IsIso r := (ConcreteCategory.isIso_iff_bijective r).mpr hbij
  have : IsIso f := by
    rw [← Spec.map_preimage f]
    infer_instance
  have hπ : π = X.isoSpec.hom ≫ f := by simp [f]
  rw [hπ]
  infer_instance

end PhilipponAlterationBaseCases

namespace PhilipponCurveAlteration

lemma regularLocalRing_of_integrallyClosed_of_dimension_le_one
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] (hdim : ringKrullDim R ≤ 1) :
    IsRegularLocalRing R := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  have hprime : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R := by
    intro P hP hp
    exact IsLocalRing.eq_maximalIdeal (hp.isMaximal_of_ne_bot hP)
  have hT : IsPrincipalIdealRing R ↔
      (IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R) :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 0 3
  letI : IsPrincipalIdealRing R := hT.mpr ⟨inferInstance, hprime⟩
  infer_instance

lemma stalk_dimension_le_topological {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact (Order.coheight_le_krullDim x).trans_eq
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm

lemma ne_genericPoint_of_isClosed_of_not_subsingleton {X : Scheme.{u}} [IsIntegral X]
    (hn : ¬ Subsingleton X) (x : X) (hx : IsClosed ({x} : Set X)) : x ≠ genericPoint X := by
  intro h
  have hclosed : IsClosed ({genericPoint X} : Set X) := h ▸ hx
  have hall : ({genericPoint X} : Set X) = Set.univ :=
    hclosed.closure_eq.symm.trans (genericPoint_spec X)
  apply hn
  refine ⟨fun a b => ?_⟩
  have ha : a = genericPoint X := Set.mem_singleton_iff.mp (hall.symm ▸ Set.mem_univ a)
  have hb : b = genericPoint X := Set.mem_singleton_iff.mp (hall.symm ▸ Set.mem_univ b)
  exact ha.trans hb.symm

lemma stalk_dimension_eq_one_of_closed {X : Scheme.{u}} [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (hn : ¬ Subsingleton X)
    (x : X) (hx : IsClosed ({x} : Set X)) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  apply le_antisymm ((stalk_dimension_le_topological x).trans hdim)
  rw [ringKrullDim_stalk_eq_coheight]
  have hne : x ≠ (⊤ : X) := ne_genericPoint_of_isClosed_of_not_subsingleton hn x hx
  have hpos : 0 < Order.coheight x := Order.coheight_pos.mpr (by
    intro hmax
    have htopx : (genericPoint X : X) ≤ x := hmax (show x ≤ genericPoint X from le_top)
    change x ⤳ genericPoint X at htopx
    exact hne ((genericPoint_specializes x).antisymm htopx).eq.symm)
  exact_mod_cast (Order.one_le_iff_ne_zero.mpr hpos.ne')

end PhilipponCurveAlteration


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open HomogeneousIdeal HomogeneousLocalization
open scoped BigOperators



set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponIntegralDimension

lemma ring_dimension_le_of_integral {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h

lemma dimension_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [show topologicalKrullDim X = Order.krullDim X from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  simp_rw [Order.krullDim_eq_iSup_coheight, ringKrullDim_stalk_eq_coheight]

lemma stalk_dimension_le {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [dimension_eq_iSup_stalk]
  exact le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) x

lemma affine_dimension_eq (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq X.isoSpec.hom X.isoSpec.hom.homeomorph.isHomeomorph

/-- An integral morphism cannot increase Krull dimension, without a finite-type hypothesis. -/
theorem dimension_le_of_integral {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [dimension_eq_iSup_stalk]
  refine iSup_le fun x => ?_
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  let W := f ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage f
  letI : IsAffine (W : Scheme) := hW
  letI : IsAffine (V : Scheme) := hV
  let z : W := ⟨x, hx⟩
  have he : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim ((W : Scheme).presheaf.stalk z) :=
    ringKrullDim_eq_of_ringEquiv
      (asIso (W.ι.stalkMap z)).commRingCatIsoToRingEquiv
  have hsec : ringKrullDim Γ(X, W) ≤ ringKrullDim Γ(Y, V) :=
    ring_dimension_le_of_integral (f.app V).hom (f.isIntegral_app V hV)
  have hdimW : topologicalKrullDim (W : Scheme) = ringKrullDim Γ(X, W) := by
    rw [affine_dimension_eq]
    exact ringKrullDim_eq_of_ringEquiv W.topIso.commRingCatIsoToRingEquiv
  have hdimV : topologicalKrullDim (V : Scheme) = ringKrullDim Γ(Y, V) := by
    rw [affine_dimension_eq]
    exact ringKrullDim_eq_of_ringEquiv V.topIso.commRingCatIsoToRingEquiv
  calc
    ringKrullDim (X.presheaf.stalk x) =
        ringKrullDim ((W : Scheme).presheaf.stalk z) := he
    _ ≤ topologicalKrullDim (W : Scheme) := stalk_dimension_le (X := (W : Scheme)) z
    _ = ringKrullDim Γ(X, W) := hdimW
    _ ≤ ringKrullDim Γ(Y, V) := hsec
    _ = topologicalKrullDim (V : Scheme) := hdimV.symm
    _ ≤ topologicalKrullDim Y := topologicalKrullDim_subspace_le Y (V : Set Y)

/-- Base change by an arbitrary algebraic field extension does not increase dimension. -/
theorem dimension_le_algebraic_baseChange
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) :
    topologicalKrullDim (pullback π (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) ≤
      topologicalKrullDim X := by
  haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact dimension_le_of_integral (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap K L))))

lemma dimension_le_of_openCover {X : Scheme.{u}} (U : X.OpenCover) (d : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (U.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  rw [dimension_eq_iSup_stalk]
  refine iSup_le fun x => ?_
  obtain ⟨i, y, rfl⟩ := U.exists_eq x
  have he : ringKrullDim (X.presheaf.stalk (U.f i y)) =
      ringKrullDim ((U.X i).presheaf.stalk y) :=
    ringKrullDim_eq_of_ringEquiv (asIso ((U.f i).stalkMap y)).commRingCatIsoToRingEquiv
  exact (he.trans_le (stalk_dimension_le (X := U.X i) y)).trans (h i)

end PhilipponIntegralDimension



set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProperCurveAlteration
open PhilipponCurveAlteration

lemma exists_projective_embedding_of_integral_subsingleton
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [Subsingleton X]
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (n : ℕ) (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
      IsClosedImmersion i ∧ i ≫ ProjSpace.π K n = π := by
  obtain ⟨D⟩ := ChowDatumProj.nonempty_of π (ChowDatum.nonempty π)
  have hU : D.U = ⊤ := by
    obtain ⟨x, hx⟩ := D.hU_dense.nonempty
    apply top_unique
    intro y _
    exact (Subsingleton.elim x y) ▸ hx
  haveI : IsIso D.U.ι := by
    rw [hU]
    change IsIso X.topIso.hom
    infer_instance
  haveI : IsIso (pullback.fst D.p D.U.ι) := inferInstance
  haveI : IsIso (pullback.fst D.p D.U.ι ≫ D.p) := by
    rw [pullback.condition]
    infer_instance
  letI : IsIso D.p := IsIso.of_isIso_comp_left (pullback.fst D.p D.U.ι) D.p
  refine ⟨D.Nd, inv D.p ≫ D.ιN, inferInstance, ?_⟩
  rw [Category.assoc, D.hoverN, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Integral proper curves and points over an algebraically closed field have smooth projective covers. -/
theorem exists_smooth_projective_cover_of_integral_proper_dimension_le_one
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      topologicalKrullDim Y ≤ 1 ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by
  classical
  by_cases hsub : Subsingleton X
  · letI := hsub
    letI : IsIso π := PhilipponAlterationBaseCases.isIso_of_integral_subsingleton_over_algClosed π
    obtain ⟨n, i, hi, hbase⟩ := exists_projective_embedding_of_integral_subsingleton K π
    refine ⟨X, 𝟙 X, inferInstance, inferInstance, inferInstance, ?_, hdim, n, i, hi, ?_⟩
    · simpa using (inferInstance : Smooth π)
    · simpa using hbase
  obtain ⟨Y, ν, hY, hnormal, hfinite, hsurj, hstalk, _⟩ :=
    exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral K π
  letI := hY
  letI := hfinite
  letI : Surjective ν := ⟨hsurj⟩
  let δ := ν ≫ π
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian δ
  have hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
    intro y
    letI := hnormal y
    apply regularLocalRing_of_integrallyClosed_of_dimension_le_one
    rw [hstalk y]
    exact (stalk_dimension_le_topological (ν y)).trans hdim
  have hsmooth : SmoothOfRelativeDimension 1 δ :=
    smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk K δ 1 (by
      intro y hy
      refine ⟨hregular y, ?_⟩
      rw [hstalk y]
      apply stalk_dimension_eq_one_of_closed hdim hsub
      have hc := ν.isClosedMap ({y} : Set Y) hy
      simpa only [Set.image_singleton] using hc)
  letI := hsmooth
  letI : Smooth δ := SmoothOfRelativeDimension.smooth 1 δ
  obtain ⟨m, j, hj, hπ⟩ := PhilipponCurveProjectivity.exists_projective_embedding_of_smooth_proper_curve K δ
  exact ⟨Y, ν, hY, inferInstance, inferInstance, inferInstance,
    (PhilipponIntegralDimension.dimension_le_of_integral ν).trans hdim, m, j, hj, hπ⟩


end PhilipponProperCurveAlteration



set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponFaithfullyFlatDimension

lemma ring_dimension_le_of_faithfullyFlat
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : ringKrullDim R ≤ ringKrullDim S := by
  classical
  simp only [ringKrullDim, Order.krullDim]
  refine iSup_le fun l => ?_
  obtain ⟨P, hP, hlo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat
    (B := S) l.last.asIdeal
  letI := hP
  letI := hlo
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  rw [← hL]
  exact le_iSup (fun l : LTSeries (PrimeSpectrum S) => (l.length : WithBot ℕ∞)) L

/-- A flat surjection cannot lower the dimension of its target. -/
lemma dimension_le_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [PhilipponIntegralDimension.dimension_eq_iSup_stalk Y]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj y
  algebraize [(f.stalkMap x).hom]
  haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact (ring_dimension_le_of_faithfullyFlat _ _).trans
    (PhilipponIntegralDimension.stalk_dimension_le (X := X) x)

end PhilipponFaithfullyFlatDimension



set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveFieldDescent

lemma fieldMap_comp
    (k K : Type u) [Field k] [Field K] [Algebra k K] (E : IntermediateField k K) :
    Spec.map (CommRingCat.ofHom (algebraMap E K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A projective scheme and a morphism to a fixed finite-type ground-field scheme
descend together, retaining the specified projective embedding. -/
theorem exists_projective_relative_finite_model
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (.of k))
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFiniteType fY]
    (X : Scheme.{u}) (fX : X ⟶ Spec (.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX]
    (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π K n = fX)
    (φ : X ⟶ Y)
    (hφ : φ ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of E))
      (g : X ⟶ X₀) (φ₀ : X₀ ⟶ Y)
      (j₀ : X₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap E K))) ∧
      IsClosedImmersion j₀ ∧ j₀ ≫ ProjSpace.π E n = f₀ ∧
      φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      g ≫ φ₀ = φ := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Pk := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
  let Q := pullback fY (ProjSpace.π k n)
  let fQ : Q ⟶ Spec (.of k) := pullback.fst fY (ProjSpace.π k n) ≫ fY
  let pbK := ProjSpace.isPullback_map k K n
  let u : X ⟶ Pk := j ≫ ProjSpace.map k K n
  have hu : u ≫ ProjSpace.π k n = fX ≫ b := by
    dsimp only [u]
    rw [Category.assoc, pbK.w, ← Category.assoc, hj]
  let α : X ⟶ Q := pullback.lift φ u (hφ.trans hu.symm)
  have hα : α ≫ fQ = fX ≫ b := by
    dsimp only [fQ]
    rw [← Category.assoc, pullback.lift_fst]
    exact hφ
  letI : CompactSpace Q :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst fY (ProjSpace.π k n))
  letI : QuasiSeparatedSpace Q :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst fY (ProjSpace.π k n))
  obtain ⟨E, hE, X₀, f₀, _hqc, _hqs, _hft, g, β, hpb, hβ, hrec⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
      k K Q fQ X fX α hα
  let v : X₀ ⟶ Pk := β ≫ pullback.snd fY (ProjSpace.π k n)
  have hv : v ≫ ProjSpace.π k n =
      f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    dsimp only [v]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hβ
  let pbE := ProjSpace.isPullback_map k E n
  let j₀ := pbE.lift v f₀ hv
  have hj₀ : j₀ ≫ ProjSpace.π E n = f₀ := pbE.lift_snd v f₀ hv
  have hj₀map : j₀ ≫ ProjSpace.map k E n = v := pbE.lift_fst v f₀ hv
  have w : ProjSpace.map k K n ≫ ProjSpace.π k n =
      (ProjSpace.π K n ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    rw [Category.assoc, fieldMap_comp]
    exact pbK.w
  let c : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E) :=
    pbE.lift (ProjSpace.map k K n)
      (ProjSpace.π K n ≫ Spec.map (CommRingCat.ofHom (algebraMap E K))) w
  have hcmap : c ≫ ProjSpace.map k E n = ProjSpace.map k K n :=
    pbE.lift_fst _ _ _
  have hcbase : c ≫ ProjSpace.π E n =
      ProjSpace.π K n ≫ Spec.map (CommRingCat.ofHom (algebraMap E K)) :=
    pbE.lift_snd _ _ _
  have hc : IsPullback c (ProjSpace.π K n) (ProjSpace.π E n)
      (Spec.map (CommRingCat.ofHom (algebraMap E K))) := by
    refine IsPullback.of_right ?_ hcbase pbE
    rw [hcmap, fieldMap_comp]
    exact pbK
  have hgj : g ≫ j₀ = j ≫ c := by
    apply pbE.hom_ext
    · rw [Category.assoc, hj₀map, Category.assoc, hcmap]
      change g ≫ (β ≫ pullback.snd fY (ProjSpace.π k n)) = u
      rw [← Category.assoc, hrec, pullback.lift_snd]
    · rw [Category.assoc, hj₀, Category.assoc, hcbase, ← Category.assoc, hj]
      exact hpb.w
  have hpj : IsPullback g j j₀ c := by
    refine IsPullback.of_bot ?_ hgj hc
    rw [hj, hj₀]
    exact hpb
  have hclosed : IsClosedImmersion j₀ :=
    AlgebraicGeometry.isClosedImmersion_of_isPullback_of_faithfullyFlat K
      (ProjSpace.π E n) (ProjSpace.π K n) c hc j₀ j g hpj inferInstance
  let φ₀ : X₀ ⟶ Y := β ≫ pullback.fst fY (ProjSpace.π k n)
  have hover : φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    dsimp only [φ₀]
    rw [Category.assoc]
    exact hβ
  have hφrec : g ≫ φ₀ = φ := by
    dsimp only [φ₀]
    rw [← Category.assoc, hrec, pullback.lift_fst]
  exact ⟨E, hE, X₀, f₀, g, φ₀, j₀, hpb, hclosed, hj₀, hover, hφrec⟩

end PhilipponProjectiveFieldDescent



set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory

namespace PhilipponFieldModelIntegral

lemma isReduced_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced Y := by
  have hstalk (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj y
    algebraize [(f.stalkMap x).hom]
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    have hf : RingHom.FaithfullyFlat (f.stalkMap x).hom := by
      change Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      infer_instance
    exact isReduced_of_injective (f.stalkMap x).hom hf.injective
  letI := hstalk
  exact isReduced_of_isReduced_stalk Y

lemma isIntegral_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsIntegral X] : IsIntegral Y := by
  letI : AlgebraicGeometry.IsReduced Y := isReduced_of_flat_surjective f
  letI : IrreducibleSpace Y := (inferInstance : Surjective f).surj.irreducibleSpace f.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

lemma geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f := by
  constructor
  intro K _ y Z fst snd hpb
  letI : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral (f := f) y fst snd hpb
  infer_instance

end PhilipponFieldModelIntegral



set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFieldModelProperties

lemma fpqc_fieldMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := by
    constructor
    intro x
    exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩
  haveI : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

lemma smooth_of_isPullback_field
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K))
    (g : X' ⟶ X)
    (h : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hs : Smooth f') : Smooth f := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K) hs


end PhilipponFieldModelProperties


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFieldModelGeometric

lemma specMap_comp_of_tower
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M] :
    Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k M)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq k L M]

/-- Geometric integrality descends along any algebraic extension of fields. -/
theorem geometricallyIntegral_of_isPullback_field
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K))
    (g : X' ⟶ X)
    (h : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [GeometricallyIntegral f'] : GeometricallyIntegral f := by
  classical
  constructor
  intro L _ s J jX jL hJ
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  letI : Algebra k L := φ.hom.toAlgebra
  let M := AlgebraicClosure L
  letI : IsScalarTower k L M := inferInstance
  let e : K →ₐ[k] M := IsAlgClosed.lift
  letI : Algebra K M := e.toRingHom.toAlgebra
  letI : IsScalarTower k K M := IsScalarTower.of_algHom e
  let aK := Spec.map (CommRingCat.ofHom (algebraMap K M))
  let aL := Spec.map (CommRingCat.ofHom (algebraMap L M))
  let ak := Spec.map (CommRingCat.ofHom (algebraMap k M))
  let P := pullback f' aK
  let p : P ⟶ Spec (.of M) := pullback.snd f' aK
  let q : P ⟶ X := pullback.fst f' aK ≫ g
  haveI : IsIntegral P :=
    GeometricallyIntegral.geometrically_isIntegral (f := f') aK _ _
      (IsPullback.of_hasPullback _ _)
  have H : IsPullback q p f ak := by
    have H₀ := (IsPullback.of_hasPullback f' aK).paste_horiz h
    dsimp only [aK] at H₀
    rw [specMap_comp_of_tower k K M] at H₀
    exact H₀
  have hAL : aL ≫ Spec.map φ = ak := specMap_comp_of_tower k L M
  have w : q ≫ f = (p ≫ aL) ≫ Spec.map φ := by
    rw [Category.assoc p aL (Spec.map φ), hAL]
    exact H.w
  let r : P ⟶ J := hJ.lift q (p ≫ aL) w
  have hr : IsPullback r p jL aL := by
    refine IsPullback.of_right ?_ (hJ.lift_snd _ _ _) hJ
    rw [hJ.lift_fst, hAL]
    exact H
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) r :=
    MorphismProperty.of_isPullback hr.flip (PhilipponFieldModelProperties.fpqc_fieldMap L M)
  letI : Surjective r := hfpqc.1.1
  letI : Flat r := hfpqc.1.2
  exact PhilipponFieldModelIntegral.isIntegral_of_flat_surjective r

end PhilipponFieldModelGeometric



set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponIntegralFiniteCurveCover

/-- An integral proper curve has an integral smooth projective cover over one finite
intermediate field of the prescribed algebraically closed algebraic extension. -/
theorem exists_integral_finite_smooth_projective_cover
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (π : C ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ GeometricallyConnected p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := (PhilipponFieldModelProperties.fpqc_fieldMap k K).1.1
  haveI : IsIntegralHom b :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  let CK := pullback π b
  let c : CK ⟶ C := pullback.fst π b
  obtain ⟨z, hz⟩ := (inferInstance : Surjective c).surj (genericPoint C)
  let S : Closeds CK := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal S
  let W := I.subscheme
  let i : W ⟶ CK := I.subschemeι
  haveI : IsIntegral W := PhilipponIntegralMultisection.integral_reduced_closure z
  let a : W ⟶ C := i ≫ c
  have hsupport : (I.support : Set CK) = closure ({z} : Set CK) := by simp [I, S]
  let wz : W := ⟨z, by
    change z ∈ (I.support : Set CK)
    rw [hsupport]
    exact subset_closure (Set.mem_singleton z)⟩
  have hgen : a wz = genericPoint C := hz
  have hsa : Surjective a := by
    constructor
    have hc : IsClosed (Set.range a) := by
      simpa only [Set.image_univ] using a.isClosedMap _ isClosed_univ
    have hall : Set.univ ⊆ Set.range a := by
      rw [← genericPoint_spec C]
      exact closure_minimal (Set.singleton_subset_iff.mpr ⟨wz, hgen⟩) hc
    exact fun x => hall (Set.mem_univ x)
  letI := hsa
  let δ : W ⟶ Spec (.of K) := i ≫ pullback.snd π b
  have hdW : topologicalKrullDim W ≤ 1 :=
    (i.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le).trans
      ((PhilipponIntegralDimension.dimension_le_algebraic_baseChange k K π).trans hdim)
  obtain ⟨Z, ν, hZ, hν, hsν, hsZ, hdZ, n, j, hj, hjbase⟩ :=
    PhilipponProperCurveAlteration.exists_smooth_projective_cover_of_integral_proper_dimension_le_one
      K δ hdW
  letI := hZ
  letI := hν
  letI := hsν
  letI := hj
  let pZ := ν ≫ δ
  let φ := ν ≫ a
  haveI : GeometricallyIntegral pZ := geometricallyIntegral_of_isAlgClosed pZ
  letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace π
  letI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated π
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace pZ
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated pZ
  have hφ : φ ≫ π = pZ ≫ b := by
    dsimp only [φ, pZ, a, δ, c]
    simp only [Category.assoc, pullback.condition]
  haveI : Surjective φ := inferInstance
  obtain ⟨E, hE, Y, p, g, f, j₀, hpb, hj₀, hj₀base, hover, hrec⟩ :=
    PhilipponProjectiveFieldDescent.exists_projective_relative_finite_model
      k K C π Z pZ n j hjbase φ hφ
  letI := hE
  letI := hj₀
  have hp : IsProper p := by rw [← hj₀base]; infer_instance
  letI := hp
  have hs : Smooth p := PhilipponFieldModelProperties.smooth_of_isPullback_field
    E K p pZ g hpb hsZ
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    MorphismProperty.of_isPullback hpb.flip (PhilipponFieldModelProperties.fpqc_fieldMap E K)
  letI : Surjective g := hfpqc.1.1
  letI : Flat g := hfpqc.1.2
  have hY : IsIntegral Y := PhilipponFieldModelIntegral.isIntegral_of_flat_surjective g
  letI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := k) E
  have hgiY : GeometricallyIntegral p :=
    PhilipponFieldModelGeometric.geometricallyIntegral_of_isPullback_field E K p pZ g hpb
  letI := hgiY
  have hgY : GeometricallyConnected p :=
    PhilipponFieldModelIntegral.geometricallyConnected_of_geometricallyIntegral p
  have hdY : topologicalKrullDim Y ≤ 1 :=
    (PhilipponFaithfullyFlatDimension.dimension_le_of_flat_surjective g).trans hdZ
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsProper (f ≫ π) := by rw [hover]; infer_instance
  have hf : IsProper f := IsProper.of_comp f π
  have hsf : Surjective f := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := (inferInstance : Surjective φ).surj x
    refine ⟨g z, ?_⟩
    change (g ≫ f) z = x
    rw [hrec]
    exact hz
  exact ⟨E, hE, Y, f, p, hY, hf, hsf, hs, hp, hgiY, hgY, hdY, hover, n, j₀, hj₀, hj₀base⟩

end PhilipponIntegralFiniteCurveCover


theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (π : C ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ GeometricallyConnected p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p := by
  exact PhilipponIntegralFiniteCurveCover.exists_integral_finite_smooth_projective_cover k K π hdim
