-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_integral_finite_multisection_of_proper_surjective
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T13:42:09.578912+00:00
-- url     : https://prove2.me/submissions/c0d8f2ea-8367-4f66-b4e5-64cae80143cd

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

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

theorem solution
    (K : Type u) [Field K] {C Z : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (p : Z ⟶ C) [IsProper p] [Surjective p] :
    ∃ (W : Scheme.{u}) (i : W ⟶ Z),
      IsIntegral W ∧ IsClosedImmersion i ∧ IsFinite (i ≫ p) ∧ Surjective (i ≫ p) := by
  classical
  let η := genericPoint C
  obtain ⟨z₀, hz₀⟩ := p.surjective η
  let q₀ : p.fiber η := (p.fiberHomeo η).symm ⟨z₀, hz₀⟩
  obtain ⟨q, _, hq⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set (p.fiber η))) ⟨q₀, trivial⟩ isClosed_univ.isLocallyClosed
  let z := p.fiberι η q
  let S : TopologicalSpace.Closeds Z := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal S
  let W := I.subscheme
  let i : W ⟶ Z := I.subschemeι
  let g := i ≫ p
  have hsupport : (I.support : Set Z) = closure ({z} : Set Z) := by simp [I, S]
  letI : IsIntegral W := PhilipponIntegralMultisection.integral_reduced_closure z
  have hdim : topologicalKrullDim W ≤ 1 := by
    change topologicalKrullDim (I.support : Set Z) ≤ 1
    rw [hsupport]
    exact PhilipponIntegralMultisection.dimension_closure_of_closed_generic_fiber
      c (SmoothOfRelativeDimension.topologicalKrullDim_le c 1) p q hq
  let wz : W := ⟨z, by
    change z ∈ (I.support : Set Z)
    rw [hsupport]
    exact subset_closure (Set.mem_singleton z)⟩
  have hgen : g wz = η := by
    change p (p.fiberι η q) = η
    exact (p.fiberHomeo η q).property
  letI : Surjective g := by
    constructor
    have hc : IsClosed (Set.range g) := by
      simpa only [Set.image_univ] using g.isClosedMap _ isClosed_univ
    have hall : Set.univ ⊆ Set.range g := by
      rw [← genericPoint_spec C]
      exact closure_minimal (Set.singleton_subset_iff.mpr ⟨wz, hgen⟩) hc
    exact fun x => hall (Set.mem_univ x)
  have hn : ¬ (Set.range g).Subsingleton := by
    intro hs
    apply PhilipponIntegralMultisection.not_subsingleton_smooth_curve c
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := g.surjective x
    obtain ⟨b, rfl⟩ := g.surjective y
    exact hs (Set.mem_range_self a) (Set.mem_range_self b)
  have hfinite := PhilipponIntegralMultisection.finite_of_dimension_le_one
    (g ≫ c) hdim c g rfl hn
  exact ⟨W, i, inferInstance, inferInstance, hfinite, inferInstance⟩
