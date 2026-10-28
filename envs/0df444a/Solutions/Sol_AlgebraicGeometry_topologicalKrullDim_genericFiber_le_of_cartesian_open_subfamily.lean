-- Prove2me | solution 1 for AlgebraicGeometry.topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T00:10:10.515166+00:00
-- url     : https://prove2.me/submissions/4f8aa039-941c-4276-bd00-5d807c66de81

import Mathlib

universe u
noncomputable section


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

end PhilipponIntegralDimension


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

end PhilipponFieldModelProperties

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
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGenericOpenFactor

/-- A dominant field point factors through every dense base open, retaining
the actual map and its dominance. -/
lemma exists_factor
    (E : Type u) [Field E] {U : Scheme.{u}} [IsIntegral U]
    (b : Spec (.of E) ⟶ U) [IsDominant b] (V : U.Opens) (hdV : Dense (V : Set U)) :
    ∃ b' : Spec (.of E) ⟶ (V : Scheme.{u}), b' ≫ V.ι = b ∧ IsDominant b' := by
  have hηV : genericPoint U ∈ V := by
    apply ((genericPoint_spec U).mem_open_set_iff V.isOpen).mpr
    simpa only [Set.univ_inter] using hdV.nonempty
  have hrange : Set.range b ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    have hz : z = genericPoint (Spec (.of E)) := Subsingleton.elim _ _
    rw [hz, PhilipponGenericDominance.genericPoint_eq_of_dominant b]
    exact hηV
  let b' := IsOpenImmersion.lift V.ι b hrange
  have hb' : b' ≫ V.ι = b := IsOpenImmersion.lift_fac V.ι b hrange
  haveI : IsDominant (b' ≫ V.ι) := by rw [hb']; infer_instance
  exact ⟨b', hb', IsDominant.of_comp_of_isOpenImmersion b' V.ι⟩

/-- The retained fraction-field chart makes the prescribed field point
factor through the dense absolute smooth base open. -/
lemma exists_factor_of_fractionField_chart
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {U N : Scheme.{u}} [IsIntegral U]
    (t : Spec (.of B) ⟶ N) [IsDominant t]
    (u : U ⟶ N) [IsOpenImmersion u]
    (b : Spec (.of E) ⟶ U)
    (hb : b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t)
    (V : U.Opens) (hdV : Dense (V : Set U)) :
    ∃ b' : Spec (.of E) ⟶ (V : Scheme.{u}), b' ≫ V.ι = b ∧ IsDominant b' := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap B E))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap B E)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective B E)]
    exact bot_le
  haveI : IsDominant (b ≫ u) := by rw [hb]; infer_instance
  haveI : IsDominant b := IsDominant.of_comp_of_isOpenImmersion b u
  exact exists_factor E b V hdV

/-- Restrict the family along a base open while retaining the same actual
generic source and its original map to the family. -/
lemma exists_cartesian_comparison_on_open
    {C Y U T : Scheme.{u}} (p : Y ⟶ U)
    (e : C ⟶ Y) (p₀ : C ⟶ T) (b : T ⟶ U)
    (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) (b' : T ⟶ (V : Scheme.{u})) (hb : b' ≫ V.ι = b) :
    ∃ e' : C ⟶ (p ⁻¹ᵁ V : Scheme.{u}),
      e' ≫ (p ⁻¹ᵁ V).ι = e ∧ IsPullback e' p₀ (p ∣_ V) b' := by
  let hr := (isPullback_morphismRestrict p V).flip
  have hcomm : e ≫ p = (p₀ ≫ b') ≫ V.ι := by
    rw [Category.assoc, hb, hp₀.w]
  let e' := hr.lift e (p₀ ≫ b') hcomm
  have he : e' ≫ (p ⁻¹ᵁ V).ι = e := hr.lift_fst _ _ _
  have hep : e' ≫ (p ∣_ V) = p₀ ≫ b' := hr.lift_snd _ _ _
  have hwhole : IsPullback (e' ≫ (p ⁻¹ᵁ V).ι) p₀ p (b' ≫ V.ι) := by
    rw [he, hb]
    exact hp₀
  exact ⟨e', he, hwhole.of_right hep hr⟩

/-- Base changing an open source subfamily gives an open subscheme of the
original actual generic source, hence cannot increase its dimension. -/
lemma dimension_le_of_open_subfamily_baseChange
    {W Y C U T : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (p : Y ⟶ U) (e : C ⟶ Y) (p₀ : C ⟶ T) (b : T ⟶ U)
    (hp₀ : IsPullback e p₀ p b) :
    topologicalKrullDim (pullback (i ≫ p) b : Scheme.{u}) ≤ topologicalKrullDim C := by
  have hr : IsPullback (pullback.fst i e) (pullback.snd i e ≫ p₀) (i ≫ p) b :=
    ((IsPullback.of_hasPullback i e).flip.paste_horiz hp₀.flip).flip
  let α := hr.isoPullback.inv ≫ pullback.snd i e
  haveI : IsOpenImmersion α := inferInstance
  exact α.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

end PhilipponGenericOpenFactor




set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponFieldPointDimension

/-- A field-valued point induces an actual faithfully flat scalar extension
of the fibre over its image point. -/
lemma dimension_fiber_le_baseChange
    (E : Type u) [Field E] {W U : Scheme.{u}}
    (p : W ⟶ U) (b : Spec (.of E) ⟶ U) :
    topologicalKrullDim (p.fiber (b (IsLocalRing.closedPoint E))) ≤
      topologicalKrullDim (pullback p b : Scheme.{u}) := by
  let η := b (IsLocalRing.closedPoint E)
  let γ : U.residueField η ⟶ CommRingCat.of E :=
    U.descResidueField (Scheme.stalkClosedPointTo b)
  have hγ : Spec.map γ ≫ U.fromSpecResidueField η = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E U b
  letI : Algebra (U.residueField η) E := γ.hom.toAlgebra
  have hf := PhilipponFieldModelProperties.fpqc_fieldMap (U.residueField η) E
  haveI : Surjective (Spec.map γ) := hf.1.1
  haveI : Flat (Spec.map γ) := hf.1.2
  let f := p.fiberToSpecResidueField η
  have hr : IsPullback
      (pullback.fst f (Spec.map γ) ≫ p.fiberι η)
      (pullback.snd f (Spec.map γ)) p b := by
    rw [← hγ]
    exact (IsPullback.of_hasPullback f (Spec.map γ)).paste_horiz
      (IsPullback.of_hasPullback p (U.fromSpecResidueField η))
  have hd : topologicalKrullDim (p.fiber η) ≤
      topologicalKrullDim (pullback f (Spec.map γ) : Scheme.{u}) :=
    PhilipponFaithfullyFlatDimension.dimension_le_of_flat_surjective
      (pullback.fst f (Spec.map γ))
  have he := hr.isoPullback.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  exact hd.trans_eq he

/-- A dominant field point controls the canonical generic fibre, without
replacing the given field or base-change scheme. -/
lemma dimension_genericFiber_le_baseChange
    (E : Type u) [Field E] {W U : Scheme.{u}} [IsIntegral U]
    (p : W ⟶ U) (b : Spec (.of E) ⟶ U) [IsDominant b] :
    topologicalKrullDim (p.fiber (genericPoint U)) ≤
      topologicalKrullDim (pullback p b : Scheme.{u}) := by
  have hη : b (IsLocalRing.closedPoint E) = genericPoint U := by
    have hz : IsLocalRing.closedPoint E = genericPoint (Spec (.of E)) := Subsingleton.elim _ _
    rw [hz]
    exact PhilipponGenericDominance.genericPoint_eq_of_dominant b
  calc
    topologicalKrullDim (p.fiber (genericPoint U)) =
        topologicalKrullDim (p.fiber (b (IsLocalRing.closedPoint E))) :=
      congrArg (fun x : U => topologicalKrullDim (p.fiber x)) hη.symm
    _ ≤ _ := dimension_fiber_le_baseChange E p b

/-- Faithfully flat extension of the residue field cannot lower fibre dimension. -/
lemma dimension_le_of_isPullback_field
    (K E : Type u) [Field K] [Field E] (γ : CommRingCat.of K ⟶ CommRingCat.of E)
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of K)) (f' : X' ⟶ Spec (.of E))
    (a : X' ⟶ X) (h : IsPullback a f' f (Spec.map γ)) :
    topologicalKrullDim X ≤ topologicalKrullDim X' := by
  letI : Algebra K E := γ.hom.toAlgebra
  have hf := PhilipponFieldModelProperties.fpqc_fieldMap K E
  haveI : Surjective a := MorphismProperty.of_isPullback h.flip hf.1.1
  haveI : Flat a := MorphismProperty.of_isPullback h.flip hf.1.2
  exact PhilipponFaithfullyFlatDimension.dimension_le_of_flat_surjective a

/-- The fibre of the original morphism is bounded by its scalar extension
at any point of an arbitrary base change. -/
lemma dimension_fiber_le_of_isPullback
    {W G U N : Scheme.{u}} (t : W ⟶ G) (p : W ⟶ U) (f : G ⟶ N) (u : U ⟶ N)
    (h : IsPullback t p f u) (x : U) :
    topologicalKrullDim (f.fiber (u x)) ≤ topologicalKrullDim (p.fiber x) := by
  exact dimension_le_of_isPullback_field (N.residueField (u x)) (U.residueField x)
    (u.residueFieldMap x) _ _ _ (isPullback_fiberToSpecResidueField_of_isPullback h x)

/-- A cartesian restriction along a dominant map controls the actual generic fibre. -/
lemma dimension_genericFiber_le_of_isPullback
    {W G U N : Scheme.{u}} [IsIntegral U] [IsIntegral N]
    (t : W ⟶ G) (p : W ⟶ U) (f : G ⟶ N) (u : U ⟶ N) [IsDominant u]
    (h : IsPullback t p f u) :
    topologicalKrullDim (f.fiber (genericPoint N)) ≤ topologicalKrullDim (p.fiber (genericPoint U)) := by
  have hη := PhilipponGenericDominance.genericPoint_eq_of_dominant u
  calc
    topologicalKrullDim (f.fiber (genericPoint N)) =
        topologicalKrullDim (f.fiber (u (genericPoint U))) :=
      congrArg (fun x : N => topologicalKrullDim (f.fiber x)) hη.symm
    _ ≤ _ := dimension_fiber_le_of_isPullback t p f u h (genericPoint U)

end PhilipponFieldPointDimension




set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGenericFiberDimensionTransport

/-- A selected open source component of a restricted family has generic
fibre bounded by the prescribed actual generic source. -/
lemma genericFiber_dimension_le_of_open_subfamily
    (E : Type u) [Field E] {Y C U W : Scheme.{u}} [IsIntegral U]
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsDominant b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) [IsIntegral (V : Scheme.{u})] (hdV : Dense (V : Set U))
    (i : W ⟶ (p ⁻¹ᵁ V : Scheme.{u})) [IsOpenImmersion i] :
    topologicalKrullDim ((i ≫ (p ∣_ V)).fiber (genericPoint (V : Scheme.{u}))) ≤
      topologicalKrullDim C := by
  obtain ⟨b', hb', hdb'⟩ := PhilipponGenericOpenFactor.exists_factor E b V hdV
  haveI : IsDominant b' := hdb'
  obtain ⟨e', _he', hp'⟩ :=
    PhilipponGenericOpenFactor.exists_cartesian_comparison_on_open p e p₀ b hp₀ V b' hb'
  exact (PhilipponFieldPointDimension.dimension_genericFiber_le_baseChange E (i ≫ (p ∣_ V)) b').trans
    (PhilipponGenericOpenFactor.dimension_le_of_open_subfamily_baseChange i (p ∣_ V) e' p₀ b' hp')

/-- The canonical generic fibre of a completed fibration is bounded by
its retained actual generic source through the two cartesian comparisons. -/
theorem genericFiber_dimension_le_of_cartesian_open_subfamily
    (E : Type u) [Field E] {Y C U W G N : Scheme.{u}} [IsIntegral U] [IsIntegral N]
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsDominant b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) [IsIntegral (V : Scheme.{u})] (hdV : Dense (V : Set U))
    (i : W ⟶ (p ⁻¹ᵁ V : Scheme.{u})) [IsOpenImmersion i]
    (t : W ⟶ G) (f : G ⟶ N) (u : (V : Scheme.{u}) ⟶ N) [IsDominant u]
    (hG : IsPullback t (i ≫ (p ∣_ V)) f u)
    (η : N) (hη : IsGenericPoint η Set.univ) :
    topologicalKrullDim (f.fiber η) ≤ topologicalKrullDim C := by
  have hηeq : η = genericPoint N := hη.eq (genericPoint_spec N)
  calc
    topologicalKrullDim (f.fiber η) = topologicalKrullDim (f.fiber (genericPoint N)) :=
      congrArg (fun x : N => topologicalKrullDim (f.fiber x)) hηeq
    _ ≤ topologicalKrullDim ((i ≫ (p ∣_ V)).fiber (genericPoint (V : Scheme.{u}))) :=
      PhilipponFieldPointDimension.dimension_genericFiber_le_of_isPullback t (i ≫ (p ∣_ V)) f u hG
    _ ≤ topologicalKrullDim C := genericFiber_dimension_le_of_open_subfamily E p b e p₀ hp₀ V hdV i

end PhilipponGenericFiberDimensionTransport

theorem solution
    (E : Type u) [Field E] {Y C U W G N : Scheme.{u}} [IsIntegral U] [IsIntegral N]
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsDominant b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) [IsIntegral (V : Scheme.{u})] (hdV : Dense (V : Set U))
    (i : W ⟶ (p ⁻¹ᵁ V : Scheme.{u})) [IsOpenImmersion i]
    (t : W ⟶ G) (f : G ⟶ N) (u : (V : Scheme.{u}) ⟶ N) [IsDominant u]
    (hG : IsPullback t (i ≫ (p ∣_ V)) f u)
    (η : N) (hη : IsGenericPoint η Set.univ) :
    topologicalKrullDim (f.fiber η) ≤ topologicalKrullDim C := by
  exact PhilipponGenericFiberDimensionTransport.genericFiber_dimension_le_of_cartesian_open_subfamily E p b e p₀ hp₀ V hdV i t f u hG η hη
