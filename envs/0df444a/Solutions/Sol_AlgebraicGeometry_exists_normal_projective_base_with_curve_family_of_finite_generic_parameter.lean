-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_base_with_curve_family_of_finite_generic_parameter
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T17:25:32.057403+00:00
-- url     : https://prove2.me/submissions/f53c0941-3031-4e6f-bbd7-15c37bd0515e

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_model_of_finite_generic_parameter_point

universe u
noncomputable section

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
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponGenericFieldPointIso

/-- A field-valued preimmersion uses exactly the residue field of its image,
via the canonical field map obtained from the actual local stalk map. -/
lemma isIso_residue_factor_of_isPreimmersion
    (E : Type u) [Field E] {U : Scheme.{u}}
    (b : Spec (.of E) ⟶ U) [IsPreimmersion b] :
    IsIso (Spec.map (U.descResidueField (Scheme.stalkClosedPointTo b))) := by
  let η := b (IsLocalRing.closedPoint E)
  let γ : U.residueField η ⟶ CommRingCat.of E :=
    U.descResidueField (Scheme.stalkClosedPointTo b)
  have hγ : Spec.map γ ≫ U.fromSpecResidueField η = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E U b
  letI : IsPreimmersion (Spec.map γ ≫ U.fromSpecResidueField η) := by rw [hγ]; infer_instance
  letI : IsPreimmersion (Spec.map γ) :=
    IsPreimmersion.of_comp (Spec.map γ) (U.fromSpecResidueField η)
  letI : Algebra (U.residueField η) E := γ.hom.toAlgebra
  have hf := PhilipponFieldModelProperties.fpqc_fieldMap (U.residueField η) E
  letI : Surjective (Spec.map γ) := hf.1.1
  letI : Flat (Spec.map γ) := hf.1.2
  letI : QuasiCompact (Spec.map γ) := hf.2
  change IsIso (Spec.map γ)
  exact Flat.isIso_of_surjective_of_mono (Spec.map γ)

/-- Fraction-field points of an affine chart are preimmersions, including
after their given open embedding into a larger integral base. -/
lemma isPreimmersion_of_fractionField_chart
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] [IsFractionRing B E]
    {N U : Scheme.{u}} (t : Spec (.of B) ⟶ N) [IsOpenImmersion t]
    (u : U ⟶ N) [IsOpenImmersion u] (b : Spec (.of E) ⟶ U)
    (hb : b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t) :
    IsPreimmersion b := by
  letI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap B E))) :=
    IsPreimmersion.of_isLocalization (R := B) (S := E) (nonZeroDivisors B)
  letI : IsPreimmersion (b ≫ u) := by rw [hb]; infer_instance
  exact IsPreimmersion.of_comp b u

end PhilipponGenericFieldPointIso


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponActualGenericFiberIso

/-- An actual generic source over a dominant field-valued preimmersion is
isomorphic to the canonical generic fibre, with both projections retained. -/
lemma exists_iso_to_genericFiber
    (E : Type u) [Field E] {X T C : Scheme.{u}} [IsIntegral T]
    (f : X ⟶ T) (t : Spec (.of E) ⟶ T) [IsDominant t] [IsPreimmersion t]
    (e : C ⟶ X) (p : C ⟶ Spec (.of E)) (hC : IsPullback e p f t) :
    ∃ γ : Spec (.of E) ⟶ Spec (T.residueField (genericPoint T)),
      IsIso γ ∧ γ ≫ T.fromSpecResidueField (genericPoint T) = t ∧
      ∃ a : C ⟶ f.fiber (genericPoint T), IsIso a ∧
        a ≫ f.fiberι (genericPoint T) = e ∧
        a ≫ f.fiberToSpecResidueField (genericPoint T) = p ≫ γ := by
  have hη : t (IsLocalRing.closedPoint E) = genericPoint T := by
    have hz : IsLocalRing.closedPoint E = genericPoint (Spec (.of E)) := Subsingleton.elim _ _
    rw [hz]
    exact PhilipponGenericDominance.genericPoint_eq_of_dominant t
  rw [← hη]
  let η := t (IsLocalRing.closedPoint E)
  let γ := Spec.map (T.descResidueField (Scheme.stalkClosedPointTo t))
  haveI : IsIso γ := PhilipponGenericFieldPointIso.isIso_residue_factor_of_isPreimmersion E t
  have hγ : γ ≫ T.fromSpecResidueField η = t :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E T t
  let hF := IsPullback.of_hasPullback f (T.fromSpecResidueField η)
  have hw : e ≫ f = (p ≫ γ) ≫ T.fromSpecResidueField η := by
    rw [Category.assoc, hγ]
    exact hC.w
  let a := hF.lift e (p ≫ γ) hw
  have ha : IsPullback a p (f.fiberToSpecResidueField η) γ := by
    refine IsPullback.of_right ?_ (hF.lift_snd _ _ _) hF
    rw [hF.lift_fst, hγ]
    exact hC
  haveI : IsIso a := ha.isIso_fst_of_isIso
  exact ⟨γ, inferInstance, hγ, a, ha.isIso_fst_of_isIso,
    hF.lift_fst _ _ _, hF.lift_snd _ _ _⟩

end PhilipponActualGenericFiberIso

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
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponFlatGenericIntegral

/-- A flat finite-type geometrically reduced family over an integral
locally noetherian base is integral when its actual generic fibre is. -/
lemma isIntegral_of_integral_genericFiber
    {X T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (f : X ⟶ T) [Flat f] [LocallyOfFiniteType f] [GeometricallyReduced f]
    [IsIntegral (f.fiber (genericPoint T))] : IsIntegral X := by
  haveI : LocallyOfFinitePresentation f :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType f
  haveI : IsReduced X := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  have hη : Dense ({genericPoint T} : Set T) := by
    rw [dense_iff_closure_eq]
    exact genericPoint_spec T
  have hd : Dense (Set.range (f.fiberι (genericPoint T))) := by
    rw [f.range_fiberι]
    exact hη.preimage f.isOpenMap
  have hi : IsIrreducible (Set.range (f.fiberι (genericPoint T))) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (f.fiber (genericPoint T))).image
        (f.fiberι (genericPoint T)) (f.fiberι (genericPoint T)).continuous.continuousOn
  haveI : IrreducibleSpace X := (irreducibleSpace_def X).mpr
    ((congrArg (fun Z : Set X => IsIrreducible Z) hd.closure_eq).mp hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end PhilipponFlatGenericIntegral


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponParameterCurveFamily

/-- Pulling back a proper flat geometrically reduced and connected parameter
family retains the prescribed smooth geometrically integral generic source.
Its total space is integral and its canonical generic fibre has the same
dimension as that source. No global smoothness of the total space is asserted. -/
theorem integral_family_of_generic_parameter_source
    (E : Type u) [Field E] {C M T C₀ : Scheme.{u}}
    [IsIntegral T] [IsLocallyNoetherian T]
    (f : C ⟶ M) [IsProper f] [Flat f] [GeometricallyReduced f] [GeometricallyConnected f]
    (b : T ⟶ M) (t : Spec (.of E) ⟶ T) [IsDominant t] [IsPreimmersion t]
    (m : Spec (.of E) ⟶ M) (htb : t ≫ b = m)
    (e₀ : C₀ ⟶ C) (p₀ : C₀ ⟶ Spec (.of E)) [Smooth p₀] [GeometricallyIntegral p₀]
    (h₀ : IsPullback e₀ p₀ f m) :
    let X := pullback f b
    let p := pullback.snd f b
    IsIntegral X ∧ IsProper p ∧ Flat p ∧ GeometricallyReduced p ∧ GeometricallyConnected p ∧
      ∃ e : C₀ ⟶ X, IsPullback e p₀ p t ∧ e ≫ pullback.fst f b = e₀ ∧
        ∃ γ : Spec (.of E) ⟶ Spec (T.residueField (genericPoint T)),
          IsIso γ ∧ γ ≫ T.fromSpecResidueField (genericPoint T) = t ∧
          ∃ a : C₀ ⟶ p.fiber (genericPoint T), IsIso a ∧
            a ≫ p.fiberι (genericPoint T) = e ∧
            a ≫ p.fiberToSpecResidueField (genericPoint T) = p₀ ≫ γ ∧
            Smooth (p.fiberToSpecResidueField (genericPoint T)) ∧
            IsProper (p.fiberToSpecResidueField (genericPoint T)) ∧
            GeometricallyIntegral (p.fiberToSpecResidueField (genericPoint T)) ∧
            topologicalKrullDim (p.fiber (genericPoint T)) = topologicalKrullDim C₀ := by
  let X := pullback f b
  let p := pullback.snd f b
  let hX := IsPullback.of_hasPullback f b
  have hw : e₀ ≫ f = (p₀ ≫ t) ≫ b := by
    rw [Category.assoc, htb]
    exact h₀.w
  let e := hX.lift e₀ (p₀ ≫ t) hw
  have he : IsPullback e p₀ p t := by
    refine IsPullback.of_right ?_ (hX.lift_snd _ _ _) hX
    rw [hX.lift_fst, htb]
    exact h₀
  obtain ⟨γ, hγ, hγt, a, ha, haf, has⟩ :=
    PhilipponActualGenericFiberIso.exists_iso_to_genericFiber E p t e p₀ he
  haveI : IsIso γ := hγ
  haveI : IsIso a := ha
  have hscomp : Smooth (a ≫ p.fiberToSpecResidueField (genericPoint T)) := by
    rw [has]
    infer_instance
  have hs : Smooth (p.fiberToSpecResidueField (genericPoint T)) :=
    (MorphismProperty.cancel_left_of_respectsIso @Smooth a _).mp hscomp
  have hgcomp : GeometricallyIntegral (a ≫ p.fiberToSpecResidueField (genericPoint T)) := by
    rw [has]
    exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral p₀ γ).mpr inferInstance
  have hg : GeometricallyIntegral (p.fiberToSpecResidueField (genericPoint T)) :=
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral a _).mp hgcomp
  haveI : GeometricallyIntegral (p.fiberToSpecResidueField (genericPoint T)) := hg
  haveI : IsIntegral (p.fiber (genericPoint T)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (p.fiberToSpecResidueField (genericPoint T))
  have hInt : IsIntegral X := PhilipponFlatGenericIntegral.isIntegral_of_integral_genericFiber p
  have hd : topologicalKrullDim (p.fiber (genericPoint T)) = topologicalKrullDim C₀ :=
    a.homeomorph.isHomeomorph.topologicalKrullDim_eq.symm
  have hp : IsProper (p.fiberToSpecResidueField (genericPoint T)) :=
    MorphismProperty.pullback_snd p (T.fromSpecResidueField (genericPoint T)) inferInstance
  exact ⟨hInt, inferInstance, inferInstance, inferInstance, inferInstance,
    e, he, hX.lift_fst _ _ _, γ, hγ, hγt, a, ha, haf, has,
    hs, hp, hg, hd⟩

end PhilipponParameterCurveFamily


set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponParameterFamilyProjective

/-- The actual pullback of a projective parameter family has a closed
projective embedding with its specified composite structure map. -/
theorem exists_closed_projective_embedding
    (k : Type u) [Field k] {C M T : Scheme.{u}}
    (πM : M ⟶ Spec (.of k)) [IsProper πM]
    (f : C ⟶ M) [IsProper f] (b : T ⟶ M) [IsProper b]
    (dC : ℕ) (iC : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dC + 1)) k))
    [IsClosedImmersion iC] (hiC : iC ≫ ProjSpace.π k dC = f ≫ πM)
    (dT : ℕ) (iT : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dT + 1)) k))
    [IsClosedImmersion iT] (hiT : iT ≫ ProjSpace.π k dT = b ≫ πM) :
    ∃ (d : ℕ) (i : pullback f b ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
      IsClosedImmersion i ∧ i ≫ ProjSpace.π k d = pullback.snd f b ≫ b ≫ πM := by
  let πC := f ≫ πM
  let πT := b ≫ πM
  have hw : pullback.fst f b ≫ πC = pullback.snd f b ≫ πT := by
    simpa only [πC, πT, Category.assoc] using
      congrArg (fun h => h ≫ πM) (pullback.condition (f := f) (g := b))
  let a := pullback.lift (pullback.fst f b) (pullback.snd f b) hw
  haveI : Mono a := by
    constructor
    intro Z u v huv
    apply pullback.hom_ext
    · simpa only [Category.assoc, a, pullback.lift_fst] using
        congrArg (fun h => h ≫ pullback.fst πC πT) huv
    · simpa only [Category.assoc, a, pullback.lift_snd] using
        congrArg (fun h => h ≫ pullback.snd πC πT) huv
  let πD := pullback.fst πC πT ≫ πC
  have he : a ≫ πD = pullback.fst f b ≫ πC := by
    simp only [πD, a, Category.assoc, pullback.lift_fst_assoc]
  haveI : IsProper (a ≫ πD) := by rw [he]; infer_instance
  haveI : IsProper a := IsProper.of_comp a πD
  haveI : IsClosedImmersion a :=
    (IsClosedImmersion.iff_isProper_and_mono a).mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨d, j, _hd, hj, hbase⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      πC πT dC iC inferInstance hiC dT iT inferInstance hiT
  haveI : IsClosedImmersion j := hj
  refine ⟨d, a ≫ j, inferInstance, ?_⟩
  calc
    _ = a ≫ πD := by simp only [Category.assoc, hbase, πD]
    _ = pullback.fst f b ≫ πC := he
    _ = _ := by simpa only [πC, πT, Category.assoc] using hw

end PhilipponParameterFamilyProjective


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponGenericParameterCurveModel

/-- A supplied projective parameter family and its actual smooth generic
curve give a global proper flat geometrically reduced connected family on
a normal projective base model. Both projective embeddings and the exact
actual generic source are retained. -/
theorem exists_projective_family_from_generic_parameter
    (k : Type u) [Field k] {S M C C₀ : Scheme.{u}} [IsIntegral S]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (dS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k dS = πS)
    (πM : M ⟶ Spec (.of k)) [IsProper πM]
    (dM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dM + 1)) k))
    [IsClosedImmersion iM] (hiM : iM ≫ ProjSpace.π k dM = πM)
    (f : C ⟶ M) [IsProper f] [Flat f] [GeometricallyReduced f] [GeometricallyConnected f]
    (dC : ℕ) (iC : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dC + 1)) k))
    [IsClosedImmersion iC] (hiC : iC ≫ ProjSpace.π k dC = f ≫ πM)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫
        S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E]
      (m : Spec (.of E) ⟶ M)
      (hm : m ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (e₀ : C₀ ⟶ C) (p₀ : C₀ ⟶ Spec (.of E)) [Smooth p₀] [GeometricallyIntegral p₀]
      (h₀ : IsPullback e₀ p₀ f m) (hd₀ : topologicalKrullDim C₀ = 1),
    ∃ (T : Scheme.{u}) (q : T ⟶ S) (b : T ⟶ M) (t : Spec (.of E) ⟶ T)
      (X : Scheme.{u}) (p : X ⟶ T) (l : X ⟶ C) (e : C₀ ⟶ X),
      IsIntegral T ∧ (∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x)) ∧
      IsProper q ∧ Surjective q ∧ IsProper b ∧ IsDominant t ∧ IsPreimmersion t ∧
      t ≫ q = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
        S.fromSpecResidueField η ∧ t ≫ b = m ∧ q ≫ πS = b ≫ πM ∧
      topologicalKrullDim T = topologicalKrullDim S ∧
      IsIntegral X ∧ IsProper p ∧ Flat p ∧ GeometricallyReduced p ∧
      GeometricallyConnected p ∧ Surjective p ∧ IsPullback l p f b ∧
      IsPullback e p₀ p t ∧ e ≫ l = e₀ ∧
      (∀ ηT : T, IsGenericPoint ηT Set.univ →
        Smooth (p.fiberToSpecResidueField ηT) ∧ IsProper (p.fiberToSpecResidueField ηT) ∧
        GeometricallyIntegral (p.fiberToSpecResidueField ηT) ∧ topologicalKrullDim (p.fiber ηT) = 1) ∧
      (∃ (dT : ℕ) (iT : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dT + 1)) k)),
        IsClosedImmersion iT ∧ iT ≫ ProjSpace.π k dT = q ≫ πS) ∧
      (∃ (dX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dX + 1)) k)),
        IsClosedImmersion iX ∧ iX ≫ ProjSpace.π k dX = p ≫ q ≫ πS) ∧
      ∃ ηT : T, IsGenericPoint ηT Set.univ ∧
        ∃ γ : Spec (.of E) ⟶ Spec (T.residueField ηT),
          IsIso γ ∧ γ ≫ T.fromSpecResidueField ηT = t ∧
          ∃ a : C₀ ⟶ p.fiber ηT, IsIso a ∧
            a ≫ p.fiberι ηT = e ∧
            a ≫ p.fiberToSpecResidueField ηT = p₀ ≫ γ := by
  letI : Algebra k (S.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫
      S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
  intro E _ _ _ _ _ m hm e₀ p₀ _ _ h₀ hd₀
  obtain ⟨T, q, b, t, hT, hnT, hq, hsq, hb, hdt, hpt, htq, htb, hcomm,
    hdim, dT, iT, hiT, hstrT⟩ :=
    AlgebraicGeometry.exists_normal_projective_model_of_finite_generic_parameter_point
      k πS dS iS hiS πM dM iM hiM η hη E m hm
  haveI : IsIntegral T := hT
  haveI : IsProper q := hq
  haveI : IsProper b := hb
  haveI : IsDominant t := hdt
  haveI : IsPreimmersion t := hpt
  haveI : IsClosedImmersion iT := hiT
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (q ≫ πS)
  let X := pullback f b
  let p := pullback.snd f b
  let l := pullback.fst f b
  obtain ⟨hX, hproper, hflat, hred, hconn, e, he, hel,
    γ, hγ, hγt, a, ha, haf, has, hsmGen, hprGen, hgeoGen, hdGen⟩ :=
    PhilipponParameterCurveFamily.integral_family_of_generic_parameter_source
      E f b t m htb e₀ p₀ h₀
  have hstrTb : iT ≫ ProjSpace.π k dT = b ≫ πM := hstrT.trans hcomm
  obtain ⟨dX, iX, hiX, hstrX⟩ :=
    PhilipponParameterFamilyProjective.exists_closed_projective_embedding
      k πM f b dC iC hiC dT iT hstrTb
  have hstrX' : iX ≫ ProjSpace.π k dX = p ≫ q ≫ πS := by
    simpa only [p, Category.assoc] using
      hstrX.trans (congrArg (fun h => pullback.snd f b ≫ h) hcomm.symm)
  have hgeneric (ηT : T) (hηT : IsGenericPoint ηT Set.univ) :
      Smooth (p.fiberToSpecResidueField ηT) ∧ IsProper (p.fiberToSpecResidueField ηT) ∧
      GeometricallyIntegral (p.fiberToSpecResidueField ηT) ∧ topologicalKrullDim (p.fiber ηT) = 1 := by
    have heq : ηT = genericPoint T := hηT.eq (genericPoint_spec T)
    exact (congrArg (fun x : T =>
      Smooth (p.fiberToSpecResidueField x) ∧ IsProper (p.fiberToSpecResidueField x) ∧
      GeometricallyIntegral (p.fiberToSpecResidueField x) ∧ topologicalKrullDim (p.fiber x) = 1) heq).mpr
        ⟨hsmGen, hprGen, hgeoGen, hdGen.trans hd₀⟩
  refine ⟨T, q, b, t, X, p, l, e, hT, hnT, hq, hsq, hb, hdt, hpt, htq, htb, hcomm,
    hdim, hX, hproper, hflat, hred, hconn, inferInstance, IsPullback.of_hasPullback f b,
    he, hel, hgeneric, ⟨dT, iT, hiT, hstrT⟩, ⟨dX, iX, hiX, hstrX'⟩,
    genericPoint T, genericPoint_spec T, γ, hγ, hγt, a, ha, haf, has⟩

end PhilipponGenericParameterCurveModel

theorem solution
    (k : Type u) [Field k] {S M C C₀ : Scheme.{u}} [IsIntegral S]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (dS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k dS = πS)
    (πM : M ⟶ Spec (.of k)) [IsProper πM]
    (dM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dM + 1)) k))
    [IsClosedImmersion iM] (hiM : iM ≫ ProjSpace.π k dM = πM)
    (f : C ⟶ M) [IsProper f] [Flat f] [GeometricallyReduced f] [GeometricallyConnected f]
    (dC : ℕ) (iC : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dC + 1)) k))
    [IsClosedImmersion iC] (hiC : iC ≫ ProjSpace.π k dC = f ≫ πM)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫
        S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E]
      (m : Spec (.of E) ⟶ M)
      (hm : m ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (e₀ : C₀ ⟶ C) (p₀ : C₀ ⟶ Spec (.of E)) [Smooth p₀] [GeometricallyIntegral p₀]
      (h₀ : IsPullback e₀ p₀ f m) (hd₀ : topologicalKrullDim C₀ = 1),
    ∃ (T : Scheme.{u}) (q : T ⟶ S) (b : T ⟶ M) (t : Spec (.of E) ⟶ T)
      (X : Scheme.{u}) (p : X ⟶ T) (l : X ⟶ C) (e : C₀ ⟶ X),
      IsIntegral T ∧ (∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x)) ∧
      IsProper q ∧ Surjective q ∧ IsProper b ∧ IsDominant t ∧ IsPreimmersion t ∧
      t ≫ q = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
        S.fromSpecResidueField η ∧ t ≫ b = m ∧ q ≫ πS = b ≫ πM ∧
      topologicalKrullDim T = topologicalKrullDim S ∧
      IsIntegral X ∧ IsProper p ∧ Flat p ∧ GeometricallyReduced p ∧
      GeometricallyConnected p ∧ Surjective p ∧ IsPullback l p f b ∧
      IsPullback e p₀ p t ∧ e ≫ l = e₀ ∧
      (∀ ηT : T, IsGenericPoint ηT Set.univ →
        Smooth (p.fiberToSpecResidueField ηT) ∧ IsProper (p.fiberToSpecResidueField ηT) ∧
        GeometricallyIntegral (p.fiberToSpecResidueField ηT) ∧ topologicalKrullDim (p.fiber ηT) = 1) ∧
      (∃ (dT : ℕ) (iT : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dT + 1)) k)),
        IsClosedImmersion iT ∧ iT ≫ ProjSpace.π k dT = q ≫ πS) ∧
      (∃ (dX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dX + 1)) k)),
        IsClosedImmersion iX ∧ iX ≫ ProjSpace.π k dX = p ≫ q ≫ πS) ∧
      ∃ ηT : T, IsGenericPoint ηT Set.univ ∧
        ∃ γ : Spec (.of E) ⟶ Spec (T.residueField ηT),
          IsIso γ ∧ γ ≫ T.fromSpecResidueField ηT = t ∧
          ∃ a : C₀ ⟶ p.fiber ηT, IsIso a ∧
            a ≫ p.fiberι ηT = e ∧
            a ≫ p.fiberToSpecResidueField ηT = p₀ ≫ γ := by
  exact PhilipponGenericParameterCurveModel.exists_projective_family_from_generic_parameter k πS dS iS hiS πM dM iM hiM f dC iC hiC η hη
