-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T22:54:41.801652+00:00
-- url     : https://prove2.me/submissions/ec7448ec-3257-409d-b62e-aacea472c68e

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of
import Theorems.Thm_AlgebraicGeometry_ChowDatum_nonempty
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_forall_isClosed_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

universe u


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

namespace PhilipponProjectiveCoordinateEmbedding

lemma localRingHom_surjective_of_graded_section
    {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (s : ℬ →+*ᵍ 𝒜) (hs : ∀ b, f (s b) = b)
    (J : Ideal B) [J.IsPrime] :
    Function.Surjective (HomogeneousLocalization.localRingHom f (J.comap f) J rfl) := by
  intro z
  obtain ⟨c, rfl⟩ := z.mk_surjective
  let d : NumDenSameDeg 𝒜 (J.comap f).primeCompl :=
    { deg := c.deg
      num := ⟨s c.num, s.2 c.num.property⟩
      den := ⟨s c.den, s.2 c.den.property⟩
      den_mem := by
        change f (s c.den) ∉ J
        rw [hs]
        exact c.den_mem }
  refine ⟨HomogeneousLocalization.mk d, ?_⟩
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.localRingHom, HomogeneousLocalization.map_mk,
    d, hs, HomogeneousLocalization.val_mk]

lemma isClosedImmersion_proj_map_of_graded_section
    {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (s : ℬ →+*ᵍ 𝒜) (hs : ∀ b, f (s b) = b)
    (hf : ℬ₊ ≤ 𝒜₊.map f) [IsProper (Proj.map f hf)] :
    IsClosedImmersion (Proj.map f hf) := by
  let m := Proj.map f hf
  have hsurj : Function.Surjective f := fun b => ⟨s b, hs b⟩
  have hinj : Function.Injective m := by
    intro x y h
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    apply Ideal.comap_injective_of_surjective f.toRingHom hsurj
    exact congrArg (fun z : ProjectiveSpectrum 𝒜 => z.asHomogeneousIdeal.toIdeal) h
  have : SurjectiveOnStalks m := by
    constructor
    intro x
    change Function.Surjective ((Proj.sheafedSpaceMap f hf).hom.stalkMap x)
    rw [← Proj.localRingHom_comp_stalkIso]
    exact ((ConcreteCategory.bijective_of_isIso (Proj.stalkIso ℬ x).inv).surjective).comp
      ((localRingHom_surjective_of_graded_section f s hs _).comp
        (ConcreteCategory.bijective_of_isIso
          (Proj.stalkIso 𝒜 (ProjectiveSpectrum.comap f hf x)).hom).surjective)
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    m.continuous hinj m.isClosedMap⟩

lemma proj_map_toSpecZero
    {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι ℬ (f s.2) (f.2 s.2.2) s.1.2 ≫
      (Proj.map f hf ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (f s.2) (f.2 s.2.2) s.1.2 ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 s.2 s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]

section Coordinates

variable {K : Type u} [CommRing K] {m n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def variableProjection (e : Fin (m + 1) ↪ Fin (n + 1)) (j : Fin (n + 1)) :
    MvPolynomial (Fin (m + 1)) K := by
  classical
  exact if h : ∃ i, e i = j then MvPolynomial.X (Classical.choose h) else 0

@[simp] lemma variableProjection_apply (e : Fin (m + 1) ↪ Fin (n + 1))
    (i : Fin (m + 1)) : variableProjection (K := K) e (e i) = MvPolynomial.X i := by
  classical
  rw [variableProjection, dif_pos ⟨i, rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ j, e j = e i from ⟨i, rfl⟩))

lemma variableProjection_homogeneous (e : Fin (m + 1) ↪ Fin (n + 1)) (j : Fin (n + 1)) :
    (variableProjection (K := K) e j).IsHomogeneous 1 := by
  classical
  unfold variableProjection
  split
  · exact MvPolynomial.isHomogeneous_X _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

def projection (e : Fin (m + 1) ↪ Fin (n + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K where
  toRingHom := MvPolynomial.eval₂Hom MvPolynomial.C (variableProjection e)
  map_mem := by
    intro d p hp
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    change (MvPolynomial.eval₂ MvPolynomial.C (variableProjection e) p).IsHomogeneous d
    simpa only [one_mul] using hp.eval₂ MvPolynomial.C (variableProjection e)
      (fun _ => MvPolynomial.isHomogeneous_C _ _) (variableProjection_homogeneous e)

def sectionMap (e : Fin (m + 1) ↪ Fin (n + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K where
  toRingHom := (MvPolynomial.rename e).toRingHom
  map_mem := by
    intro d p hp
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    exact hp.rename_isHomogeneous

@[simp] lemma projection_X (e : Fin (m + 1) ↪ Fin (n + 1)) (i : Fin (m + 1)) :
    projection (K := K) e (MvPolynomial.X (e i)) = MvPolynomial.X i := by
  simp [projection]

@[simp] lemma projection_C (e : Fin (m + 1) ↪ Fin (n + 1)) (r : K) :
    projection e (MvPolynomial.C r) = MvPolynomial.C r := by simp [projection]

lemma projection_section (e : Fin (m + 1) ↪ Fin (n + 1)) (p : MvPolynomial (Fin (m + 1)) K) :
    projection e (sectionMap e p) = p := by
  have h : (projection (K := K) e).toRingHom.comp (sectionMap e).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sectionMap]
    · intro i
      simp [sectionMap]
  exact congrArg (fun f : MvPolynomial (Fin (m + 1)) K →+* MvPolynomial _ K => f p) h

lemma irrelevant_le_map_projection (e : Fin (m + 1) ↪ Fin (n + 1)) :
    (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)₊ ≤
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)₊.map (projection e) := by
  rw [← toIdeal_le_toIdeal_iff]
  apply le_trans (ProjSpace.irrelevant_le_span_X K m)
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← projection_X e i]
  apply Ideal.mem_map_of_mem
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < 1 by omega) (ProjSpace.X_mem_one K n (e i))

def coordinateEmbedding (e : Fin (m + 1) ↪ Fin (n + 1)) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) :=
  Proj.map (projection e) (irrelevant_le_map_projection e)

@[reassoc] lemma coordinateEmbedding_comp_pi (e : Fin (m + 1) ↪ Fin (n + 1)) :
    coordinateEmbedding (K := K) e ≫ ProjSpace.π K n = ProjSpace.π K m := by
  unfold coordinateEmbedding ProjSpace.π
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact projection_C e r

instance coordinateEmbedding_isClosedImmersion (e : Fin (m + 1) ↪ Fin (n + 1)) :
    IsClosedImmersion (coordinateEmbedding (K := K) e) := by
  have : IsProper (coordinateEmbedding (K := K) e ≫ ProjSpace.π K n) := by
    rw [coordinateEmbedding_comp_pi]
    infer_instance
  have hproper : IsProper (coordinateEmbedding (K := K) e) :=
    IsProper.of_comp _ (ProjSpace.π K n)
  change IsProper (Proj.map (projection e) (irrelevant_le_map_projection e)) at hproper
  letI := hproper
  exact isClosedImmersion_proj_map_of_graded_section
    (projection e) (sectionMap e) (projection_section e) _

lemma X_mem_coordinateEmbedding_of_not_mem (e : Fin (m + 1) ↪ Fin (n + 1))
    (j : Fin (n + 1)) (hj : j ∉ Set.range e)
    (x : Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)) :
    MvPolynomial.X j ∈ (coordinateEmbedding e x).asHomogeneousIdeal := by
  change projection e (MvPolynomial.X j) ∈ x.asHomogeneousIdeal
  simp [projection, variableProjection, show ¬ ∃ i, e i = j from hj]

lemma disjoint_range_coordinateEmbedding {l : ℕ}
    (e : Fin (m + 1) ↪ Fin (n + 1)) (f : Fin (l + 1) ↪ Fin (n + 1))
    (hef : Disjoint (Set.range e) (Set.range f)) :
    Disjoint (Set.range (coordinateEmbedding (K := K) e))
      (Set.range (coordinateEmbedding (K := K) f)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have hvars : ∀ j : Fin (n + 1),
      MvPolynomial.X j ∈ (coordinateEmbedding (K := K) e x).asHomogeneousIdeal := by
    intro j
    by_cases hj : j ∈ Set.range e
    · rw [← hy]
      exact X_mem_coordinateEmbedding_of_not_mem f j
        (fun h => Set.disjoint_left.mp hef hj h) y
    · exact X_mem_coordinateEmbedding_of_not_mem e j hj x
  apply (coordinateEmbedding (K := K) e x).not_irrelevant_le
  apply le_trans (ProjSpace.irrelevant_le_span_X K n)
  exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hvars j)

end Coordinates

lemma exists_disjoint_coordinate_embeddings {A : Type u} [Fintype A] (d : A → ℕ) :
    ∃ (N : ℕ) (e : ∀ a, Fin (d a + 1) ↪ Fin (N + 1)),
      Pairwise (fun a b => Disjoint (Set.range (e a)) (Set.range (e b))) := by
  classical
  let B := Σ a, Fin (d a + 1)
  let e₀ : B ↪ Fin (Fintype.card B + 1) :=
    (Fintype.equivFin B).toEmbedding.trans Fin.castSuccEmb
  let e (a : A) : Fin (d a + 1) ↪ Fin (Fintype.card B + 1) :=
    (Function.Embedding.sigmaMk a).trans e₀
  refine ⟨Fintype.card B, e, ?_⟩
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  apply hab
  have heq : (⟨a, i⟩ : B) = ⟨b, j⟩ := e₀.injective (hi.trans hj.symm)
  exact congrArg Sigma.fst heq

end PhilipponProjectiveCoordinateEmbedding

namespace PhilipponIntegralProjectiveCover
lemma integral_vanishing_subscheme {X : Scheme.{u}} (S : Closeds X)
    (hS : IsIrreducible (S : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have : AlgebraicGeometry.IsReduced I.subscheme :=
    PhilipponIntegralMultisection.reduced_vanishing_subscheme S
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    have hs : (I.support : Set X) = S := by simp [I]
    rw [hs]
    exact Subtype.irreducibleSpace hS
  exact isIntegral_of_irreducibleSpace_of_isReduced _

open scoped Function in
lemma isClosedImmersion_sigmaDesc {A : Type u} [Finite A]
    {Y : A → Scheme.{u}} {X : Scheme.{u}} (f : ∀ a, Y a ⟶ X)
    [∀ a, IsClosedImmersion (f a)]
    (hf : Pairwise (Disjoint on (Set.range <| f ·))) :
    IsClosedImmersion (Sigma.desc f) := by
  have : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) (fun _ => inferInstance)
  constructor
  suffices Topology.IsClosedEmbedding (Sigma.desc f ∘ sigmaMk Y) by
    convert! this.comp (sigmaMk Y).symm.isClosedEmbedding using 1
    ext x
    simp
  refine .of_continuous_injective_isClosedMap ?_ ?_ ?_
  · fun_prop
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hxy : f a x = f b y := by
      simpa [← Scheme.Hom.comp_apply] using h
    obtain rfl : a = b := by
      by_contra hne
      exact Set.disjoint_iff_forall_ne.mp (hf hne) ⟨x, rfl⟩ ⟨y, hxy.symm⟩ rfl
    rw [(f a).isClosedEmbedding.injective hxy]
  · intro S hS
    have heq : (Sigma.desc f ∘ sigmaMk Y) '' S =
        ⋃ a, (f a) '' ((fun x : Y a => (⟨a, x⟩ : Σ b, Y b)) ⁻¹' S) := by
      ext z
      simp only [Set.mem_image, Set.mem_iUnion, Sigma.exists]
      constructor
      · rintro ⟨a, x, hx, rfl⟩
        refine ⟨a, x, hx, ?_⟩
        simp [← Scheme.Hom.comp_apply]
      · rintro ⟨a, x, hx, rfl⟩
        refine ⟨a, x, hx, ?_⟩
        simp [← Scheme.Hom.comp_apply]
    rw [heq]
    exact isClosed_iUnion_of_finite (fun a =>
      (f a).isClosedEmbedding.isClosedMap _ (hS.preimage continuous_sigmaMk))

theorem exists_projective_embedding_sigma {K : Type u} [CommRing K]
    {A : Type u} [Fintype A] (Y : A → Scheme.{u})
    (π : ∀ a, Y a ⟶ Spec (.of K)) (d : A → ℕ)
    (j : ∀ a, Y a ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d a + 1)) K))
    [∀ a, IsClosedImmersion (j a)] (hj : ∀ a, j a ≫ ProjSpace.π K (d a) = π a) :
    ∃ (N : ℕ) (i : (∐ Y) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)),
      IsClosedImmersion i ∧ i ≫ ProjSpace.π K N = Sigma.desc π := by
  classical
  obtain ⟨N, e, he⟩ :=
    PhilipponProjectiveCoordinateEmbedding.exists_disjoint_coordinate_embeddings d
  let f (a : A) := j a ≫ PhilipponProjectiveCoordinateEmbedding.coordinateEmbedding (e a)
  letI (a : A) : IsClosedImmersion (f a) := inferInstance
  have hdisj : Pairwise (fun a b => Disjoint (Set.range (f a)) (Set.range (f b))) := by
    intro a b hab
    apply (PhilipponProjectiveCoordinateEmbedding.disjoint_range_coordinateEmbedding
      (K := K) (e a) (e b) (he hab)).mono
    · rintro _ ⟨x, rfl⟩
      exact ⟨j a x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨j b x, rfl⟩
  refine ⟨N, Sigma.desc f, isClosedImmersion_sigmaDesc f hdisj, ?_⟩
  apply Sigma.hom_ext
  intro a
  simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
  change (j a ≫ PhilipponProjectiveCoordinateEmbedding.coordinateEmbedding (e a)) ≫
    ProjSpace.π K N = π a
  rw [Category.assoc,
    PhilipponProjectiveCoordinateEmbedding.coordinateEmbedding_comp_pi, hj]

end PhilipponIntegralProjectiveCover


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
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponGeometricCurveCover

lemma exists_finite_integral_closed_family (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] :
    ∃ (A : Type u) (_ : Fintype A) (C : A → Scheme.{u}) (ι : ∀ a, C a ⟶ X),
      (∀ a, IsIntegral (C a)) ∧ (∀ a, IsClosedImmersion (ι a)) ∧
      (∀ a, topologicalKrullDim (C a) ≤ topologicalKrullDim X) ∧
      (⋃ a, Set.range (ι a)) = Set.univ := by
  classical
  let A := irreducibleComponents X
  letI : Fintype A := NoetherianSpace.finite_irreducibleComponents.fintype
  let S (a : A) : Closeds X := ⟨a.val, isClosed_of_mem_irreducibleComponents _ a.property⟩
  let I (a : A) := Scheme.IdealSheafData.vanishingIdeal (S a)
  let C (a : A) := (I a).subscheme
  let ι (a : A) : C a ⟶ X := (I a).subschemeι
  have hC (a : A) : IsIntegral (C a) :=
    PhilipponIntegralProjectiveCover.integral_vanishing_subscheme (S a) a.property.1
  have hι (a : A) : IsClosedImmersion (ι a) := inferInstance
  have hdim (a : A) : topologicalKrullDim (C a) ≤ topologicalKrullDim X :=
    (ι a).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  refine ⟨A, inferInstance, C, ι, hC, hι, hdim, ?_⟩
  have hrange (a : A) : Set.range (ι a) = a.val := by
    change Set.range (I a).subschemeι = a.val
    rw [(I a).range_subschemeι]
    simp [I, S]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  let a : A := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  apply Set.mem_iUnion.mpr
  refine ⟨a, ?_⟩
  rw [hrange a]
  exact mem_irreducibleComponent

/-- Proper schemes of dimension at most one, including reducible and nonreduced schemes,
have a smooth projective cover of dimension at most one over an algebraically closed field. -/
theorem exists_smooth_projective_cover_of_proper_dimension_le_one
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧ topologicalKrullDim Y ≤ 1 ∧
      ∃ (n : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π K n = f ≫ π := by
  classical
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨A, hA, C, ι, hC, hι, hdC, hsurj⟩ := exists_finite_integral_closed_family X
  letI := hA
  letI (a : A) := hC a
  letI (a : A) := hι a
  have each (a : A) :=
    PhilipponProperCurveAlteration.exists_smooth_projective_cover_of_integral_proper_dimension_le_one
      K (ι a ≫ π) ((hdC a).trans hdim)
  choose Z g hZ hg hgs hsmooth hdZ n j hj hover using each
  letI (a : A) := hg a
  letI (a : A) := hgs a
  letI (a : A) := hsmooth a
  letI (a : A) := hj a
  let q (a : A) := g a ≫ (ι a ≫ π)
  let p (a : A) := g a ≫ ι a
  let d : (∐ Z) ⟶ X := Sigma.desc p
  have hd : d ≫ π = Sigma.desc q := by
    apply Sigma.hom_ext
    intro a
    simp [d, p, q]
  obtain ⟨N, i, hi, hiq⟩ :=
    PhilipponIntegralProjectiveCover.exists_projective_embedding_sigma Z q n j hover
  letI := hi
  have hproper : IsProper (d ≫ π) := by
    rw [hd, ← hiq]
    infer_instance
  letI := hproper
  have hp : IsProper d := IsProper.of_comp d π
  have hsd : Smooth (d ≫ π) := by
    rw [hd]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth) (fun a => hsmooth a)
  have hsurjd : Surjective d := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    have hprange (a : A) : Set.range (p a) = Set.range (ι a) :=
      range_eq_range_of_surjective (p a) (ι a) (g a) rfl
    simpa only [hprange] using hsurj
  have hdimZ : topologicalKrullDim (∐ Z : Scheme.{u}) ≤ 1 :=
    PhilipponIntegralDimension.dimension_le_of_openCover (sigmaOpenCover Z) 1 hdZ
  exact ⟨∐ Z, d, hp, hsurjd, hsd, hdimZ, N, i, hi, by rw [hd]; exact hiq⟩

/-- An algebraic extension to an algebraically closed field yields a smooth projective
cover of the actual base-changed proper scheme of dimension at most one. -/
theorem exists_smooth_projective_geometric_curve_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed L] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π]
    (hdim : topologicalKrullDim X ≤ 1) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
    ∃ (Y : Scheme.{u}) (f : Y ⟶ pullback π b),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ pullback.snd π b) ∧
      topologicalKrullDim Y ≤ 1 ∧
      ∃ (n : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) L)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π L n = f ≫ pullback.snd π b := by
  dsimp only
  exact exists_smooth_projective_cover_of_proper_dimension_le_one L (pullback.snd π _)
    ((PhilipponIntegralDimension.dimension_le_algebraic_baseChange K L π).trans hdim)

end PhilipponGeometricCurveCover


theorem solution
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed L] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π]
    (hdim : topologicalKrullDim X ≤ 1) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
    ∃ (Y : Scheme.{u}) (f : Y ⟶ pullback π b),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ pullback.snd π b) ∧
      topologicalKrullDim Y ≤ 1 ∧
      ∃ (n : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) L)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π L n = f ≫ pullback.snd π b := by
  exact PhilipponGeometricCurveCover.exists_smooth_projective_geometric_curve_cover K L π hdim
