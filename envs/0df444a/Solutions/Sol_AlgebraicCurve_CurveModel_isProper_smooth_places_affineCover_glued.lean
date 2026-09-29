-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9ffe100d-3da8-5ce4-b4b8-460f026a93eb

import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField AlgebraicCurve IsLocalRing
open AlgebraicCurve.CurveModel

set_option autoImplicit false

noncomputable section

universe u

section ChartRings

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

private theorem adjoin_inv_eq_adjoin (t : L) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  refine le_antisymm ?_ ?_
  · exact adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self K t))
  · refine adjoin_simple_le_iff.mpr ?_
    have h : t = (t⁻¹)⁻¹ := (inv_inv t).symm
    rw [h]
    exact inv_mem (by rw [← h]; exact mem_adjoin_simple_self K t⁻¹)

private scoped instance finiteDimensional_adjoin_inv (t : L) [FiniteDimensional K⟮t⟯ L] :
    FiniteDimensional K⟮t⁻¹⟯ L := by
  rw [adjoin_inv_eq_adjoin K t]; infer_instance

private scoped instance isSeparable_adjoin_inv (t : L) [Algebra.IsSeparable K⟮t⟯ L] :
    Algebra.IsSeparable K⟮t⁻¹⟯ L := by
  rw [adjoin_inv_eq_adjoin K t]; infer_instance

open scoped IntermediateField.algebraAdjoinAdjoin in

private scoped instance isDedekindDomain_chartRing_of_isSeparable (s : L) [FiniteDimensional K⟮s⟯ L]
    [Algebra.IsSeparable K⟮s⟯ L] : IsDedekindDomain (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in

private scoped instance finite_chartRing_of_isSeparable (s : L) [FiniteDimensional K⟮s⟯ L]
    [Algebra.IsSeparable K⟮s⟯ L] :
    Module.Finite (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.finite (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

private scoped instance finiteType_chartRing_of_isSeparable (s : L) [FiniteDimensional K⟮s⟯ L]
    [Algebra.IsSeparable K⟮s⟯ L] : Algebra.FiniteType K (chartRing K ({s} : Set L)) :=
  (Algebra.FiniteType.adjoin_of_finite (R := K) (Set.finite_singleton s)).trans
    (inferInstance : Algebra.FiniteType (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)))

private scoped instance isNoetherianRing_chartRing_of_isSeparable (s : L) [FiniteDimensional K⟮s⟯ L]
    [Algebra.IsSeparable K⟮s⟯ L] : IsNoetherianRing (chartRing K ({s} : Set L)) :=
  inferInstance

end ChartRings

section Glued

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]

private theorem locallyOfFiniteType_gluedToBase_of_isSeparable [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L] : LocallyOfFiniteType (gluedToBase K t) := by
  have h₀' : LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t) := by
    rw [ι₀_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t) := by
    rw [ιInf_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (Limits.span (f₀ K t) (fInf K t))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (Limits.span (f₀ K t) (fInf K t))).f none ≫
        gluedToBase K t = f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t) := by
      show Limits.colimit.ι (Limits.span (f₀ K t) (fInf K t)) none ≫ gluedToBase K t = _
      rw [← Limits.colimit.w (Limits.span (f₀ K t) (fInf K t)) Limits.WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs (LocallyOfFiniteType (f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t)))
  · change LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t)
    exact h₀'
  · change LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t)
    exact hInf'

private theorem isLocallyNoetherian_glued_of_isSeparable [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L] : IsLocallyNoetherian (glued K t) := by
  refine (isLocallyNoetherian_iff_openCover (X := glued K t)
    (Scheme.IsLocallyDirected.openCover (Limits.span (f₀ K t) (fInf K t)))).mpr ?_
  rintro (_ | _ | _)
  · change IsLocallyNoetherian (XOverlap K t)
    haveI : IsNoetherianRing (chartRing K ({t, t⁻¹} : Set L)) := by
      letI := (incl₀ K t).toRingHom.toAlgebra
      haveI := isLocalization_away_incl₀ K t (Fact.out : t ≠ 0)
      exact IsLocalization.isNoetherianRing (Submonoid.powers (tChart K t)) _ inferInstance
    infer_instance
  · change IsLocallyNoetherian (X₀ K t)
    infer_instance
  · change IsLocallyNoetherian (XInf K t)
    infer_instance

private theorem quasiSeparated_gluedToBase_of_isSeparable [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L] : QuasiSeparated (gluedToBase K t) :=
  haveI := isLocallyNoetherian_glued_of_isSeparable K t
  QuasiSeparated.of_quasiSeparatedSpace _

private theorem hasLift_generic_of_mem_pullbackVS [FiniteDimensional K⟮t⟯ L]
    (S : ValuativeCommSq (gluedToBase K t))
    (φ : (glued K t).presheaf.stalk (genericPoint (glued K t)) ⟶ CommRingCat.of S.K)
    (s : L) (i : chartRing K ({s} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L))
    (hi : ∀ a : chartRing K ({s} : Set L), (i a : L) = a)
    (ιA : Spec (CommRingCat.of (chartRing K ({s} : Set L))) ⟶ glued K t) [IsOpenImmersion ιA]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
    (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t)))
    (hs : s ∈ pullbackVS K t S φ) : S.commSq.HasLift := by
  have hK : ∀ a : K, algebraMap K L a ∈ pullbackVS K t S φ :=
    algebraMap_mem_pullbackVS K t S φ h₁
  let q : Spec (CommRingCat.of (chartRing K ({s} : Set L))) :=
    ⟨centre K s (pullbackVS K t S φ) hK hs, centre_isPrime K s (pullbackVS K t S φ) hK hs⟩
  refine hasLift_of_range K t S (genericPoint_specializes (ιA.base q)) φ h₁ fun u => ?_
  have hmem : (gluedFunctionFieldEquiv K t).symm
      (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField u) ∈
        pullbackVS K t S φ := by
    have hr : (gluedFunctionFieldEquiv K t).symm
        (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField u) ∈
        ((((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField)).range :
            Set L) := ⟨u, rfl⟩
    rw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({s} : Set L)) i hi ιA comm q]
      at hr
    obtain ⟨a, b, hb, e⟩ := hr
    rw [e]
    apply (pullbackVS K t S φ).mem_of_valuation_le_one
    have hb' : b ∉ centre K s (pullbackVS K t S φ) hK hs := hb
    rw [map_mul, map_inv₀, valuation_eq_one_of_not_mem_centre K s (pullbackVS K t S φ) hK hs hb',
      inv_one, mul_one]
    exact valuation_coe_le_one K s (pullbackVS K t S φ) hK hs a
  rw [mem_pullbackVS_iff, gL_ffEquiv_symm] at hmem
  exact hmem

private theorem hasLift_of_generic [FiniteDimensional K⟮t⟯ L]
    (S : ValuativeCommSq (gluedToBase K t))
    (hgen : S.i₁.base (IsLocalRing.closedPoint S.K) = genericPoint (glued K t)) :
    S.commSq.HasLift := by
  obtain ⟨φ, -, h₁⟩ := exists_eq_SpecMap_comp_fromSpecStalk K t S.i₁ hgen
  rcases (pullbackVS K t S φ).mem_or_inv_mem t with ht | ht
  · exact hasLift_generic_of_mem_pullbackVS K t S φ t (incl₀ K t) (fun a => coe_chartIncl K _ a)
      (ι₀ K t) rfl h₁ ht
  · exact hasLift_generic_of_mem_pullbackVS K t S φ t⁻¹ (inclInf K t)
      (fun a => coe_chartIncl K _ a) (ιInf K t) (glue_condition K t).symm h₁ ht

section Chart

variable (A : Subalgebra K L) (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
  (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
  (φ : (glued K t).presheaf.stalk (ιA.base p) ⟶ CommRingCat.of S.K)

include ιA_toBase in
private theorem gA_mem_range_of_isMaximal [Algebra.FiniteType K A] [IsLocalHom φ.hom]
    [p.asIdeal.IsMaximal]
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p)) (a : A) :
    gA K t A ιA S p φ a ∈ (algebraMap S.R S.K).range := by
  letI := Ideal.Quotient.field p.asIdeal
  haveI : Module.Finite K (A ⧸ p.asIdeal) := finite_of_finite_type_of_isJacobsonRing K _
  haveI : IsIntegrallyClosed S.R := GCDMonoid.toIsIntegrallyClosed
  let β : K →+* S.R := (Spec.preimage S.i₂).hom
  let gbar : A ⧸ p.asIdeal →+* S.K :=
    Ideal.Quotient.lift p.asIdeal (gA K t A ιA S p φ) (gA_eq_zero K t A ιA S p φ)
  have hg : gA K t A ιA S p φ a = gbar (Ideal.Quotient.mk p.asIdeal a) :=
    (Ideal.Quotient.lift_mk _ _ _).symm
  have hcomp : (algebraMap S.R S.K).comp β = gbar.comp (algebraMap K (A ⧸ p.asIdeal)) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.lift_mk]
    exact (gA_algebraMap K t A ιA ιA_toBase S p φ h₁ c).symm
  obtain ⟨f, hf, hfa⟩ : IsIntegral K (Ideal.Quotient.mk p.asIdeal a) :=
    Algebra.IsIntegral.isIntegral _
  have hint : IsIntegral S.R (gA K t A ιA S p φ a) := by
    refine ⟨f.map β, hf.map β, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, hg, ← Polynomial.hom_eval₂]
    change gbar (Polynomial.eval₂ (algebraMap K (A ⧸ p.asIdeal)) _ f) = 0
    rw [hfa, map_zero]
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hint

include ιA_toBase in
private theorem mem_range_of_isMaximal [Algebra.FiniteType K A] [IsLocalHom φ.hom]
    [p.asIdeal.IsMaximal]
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p))
    (x : (glued K t).presheaf.stalk (ιA.base p)) : φ x ∈ (algebraMap S.R S.K).range := by
  obtain ⟨y, rfl⟩ : ∃ y, (stalkChartEquiv K t A ιA p).symm y = x :=
    ⟨stalkChartEquiv K t A ιA p x, RingEquiv.symm_apply_apply _ _⟩
  change φA K t A ιA S p φ y ∈ _
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl y
  obtain ⟨c, hc⟩ := exists_gA_mul_gA_eq_one K t A ιA S p φ b b.2
  have hspec := congrArg (φA K t A ιA S p φ)
    (IsLocalization.mk'_spec ((Spec (CommRingCat.of A)).presheaf.stalk p) a b)
  rw [map_mul] at hspec
  have hspec' : φA K t A ιA S p φ (IsLocalization.mk' _ a b) * gA K t A ιA S p φ b =
      gA K t A ιA S p φ a := hspec
  have key : φA K t A ιA S p φ (IsLocalization.mk' _ a b) =
      gA K t A ιA S p φ a * gA K t A ιA S p φ c := by
    calc φA K t A ιA S p φ (IsLocalization.mk' _ a b)
        = φA K t A ιA S p φ (IsLocalization.mk' _ a b) *
            (gA K t A ιA S p φ b * gA K t A ιA S p φ c) := by rw [hc, mul_one]
      _ = (φA K t A ιA S p φ (IsLocalization.mk' _ a b) * gA K t A ιA S p φ b) *
            gA K t A ιA S p φ c := by ring
      _ = gA K t A ιA S p φ a * gA K t A ιA S p φ c := by rw [hspec']
  rw [key]
  exact Subring.mul_mem _ (gA_mem_range_of_isMaximal K t A ιA ιA_toBase S p φ h₁ a)
    (gA_mem_range_of_isMaximal K t A ιA ιA_toBase S p φ h₁ c)

end Chart

private theorem hasLift_closed_of_isMaximal (A : Subalgebra K L) [Algebra.FiniteType K A]
    (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
    (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
    (hp : S.i₁.base (IsLocalRing.closedPoint S.K) = ιA.base p) (hmax : p.asIdeal.IsMaximal) :
    S.commSq.HasLift := by
  obtain ⟨φ, hloc, h₁⟩ := exists_eq_SpecMap_comp_fromSpecStalk K t S.i₁ hp
  haveI := hloc
  haveI := hmax
  exact hasLift_of_range K t S (specializes_refl _) φ h₁ fun _ =>
    mem_range_of_isMaximal K t A ιA ιA_toBase S p φ h₁ _

private theorem valuativeCriterion_existence_of_isSeparable [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L] : ValuativeCriterion.Existence (gluedToBase K t) := by
  intro S
  rcases mem_range_ι₀_or_mem_range_ιInf K t (S.i₁.base (IsLocalRing.closedPoint S.K)) with
    ⟨p, hp⟩ | ⟨q, hq⟩
  · by_cases hbot : p.asIdeal = ⊥
    · refine hasLift_of_generic K t S ?_
      have hη : p = genericPoint (X₀ K t) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      rw [← hp, hη]
      exact genericPoint_eq_of_isOpenImmersion (ι₀ K t)
    · exact hasLift_closed_of_isMaximal K t (chartRing K ({t} : Set L)) (ι₀ K t)
        (ι₀_gluedToBase K t) S p hp.symm (Ideal.IsPrime.isMaximal p.isPrime hbot)
  · by_cases hbot : q.asIdeal = ⊥
    · refine hasLift_of_generic K t S ?_
      have hη : q = genericPoint (XInf K t) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      rw [← hq, hη]
      exact genericPoint_eq_of_isOpenImmersion (ιInf K t)
    · exact hasLift_closed_of_isMaximal K t (chartRing K ({t⁻¹} : Set L)) (ιInf K t)
        (ιInf_gluedToBase K t) S q hq.symm (Ideal.IsPrime.isMaximal q.isPrime hbot)

private theorem isProper_gluedToBase_of_isSeparable [FiniteDimensional K⟮t⟯ L]
    [Algebra.IsSeparable K⟮t⟯ L] : IsProper (gluedToBase K t) :=
  haveI := quasiSeparated_gluedToBase_of_isSeparable K t
  haveI := locallyOfFiniteType_gluedToBase_of_isSeparable K t
  IsProper.of_valuativeCriterion (gluedToBase K t)
    ((ValuativeCriterion.iff).mpr
      ⟨valuativeCriterion_existence_of_isSeparable K t, valuativeCriterion_uniqueness K t⟩)

end Glued

namespace S7A8SM

p2m_open "CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial Algebra CategoryTheory.Algebra IntermediateField"
open AlgebraicCurve.CurveModel
open scoped AlgebraicCurve.CurveModel
open scoped IntermediateField.algebraAdjoinAdjoin

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

section OneGenerator

variable (s : L) [FiniteDimensional ↥K⟮s⟯ L] [Algebra.IsSeparable ↥K⟮s⟯ L]

private scoped instance isDedekindDomain_chartRing_sm : IsDedekindDomain ↥(chartRing K ({s} : Set L)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin K ({s} : Set L)) ↥K⟮s⟯ L _

private scoped instance finite_chartRing_sm :
    Module.Finite ↥(Algebra.adjoin K ({s} : Set L)) ↥(chartRing K ({s} : Set L)) :=
  IsIntegralClosure.finite (Algebra.adjoin K ({s} : Set L)) ↥K⟮s⟯ L _

private scoped instance isFractionRing_chartRing_sm : IsFractionRing ↥(chartRing K ({s} : Set L)) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin K ({s} : Set L)) ↥K⟮s⟯ L _

private scoped instance finiteType_chartRing_sm : Algebra.FiniteType K ↥(chartRing K ({s} : Set L)) :=
  (Algebra.FiniteType.adjoin_of_finite (R := K) (Set.finite_singleton s)).trans
    (inferInstance :
      Algebra.FiniteType ↥(Algebra.adjoin K ({s} : Set L)) ↥(chartRing K ({s} : Set L)))

private scoped instance chartRing_finitePresentation' : FinitePresentation K ↥(chartRing K ({s} : Set L)) :=
  (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance

attribute [local instance] Ideal.Quotient.field

private theorem formallySmooth_chartRing_localization_closed' [PerfectField K]
    (𝔪 : Ideal ↥(chartRing K ({s} : Set L))) [𝔪.IsPrime] (h𝔪 : 𝔪 ≠ ⊥) :
    FormallySmooth K (Localization.AtPrime 𝔪) := by
  haveI h𝔪max : 𝔪.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔪
  obtain ⟨u, hu𝔪, hu0, hspan⟩ := exists_mem_and_maximalIdeal_eq_span 𝔪 h𝔪
  have hu : Transcendental K u := transcendental_of_mem K h𝔪max.ne_top hu𝔪 hu0

  letI alg : Algebra K[X] (chartRing K ({s} : Set L)) :=
    (Polynomial.aeval u : K[X] →ₐ[K] chartRing K ({s} : Set L)).toRingHom.toAlgebra
  have halg : ∀ f : K[X], algebraMap K[X] (chartRing K ({s} : Set L)) f = Polynomial.aeval u f :=
    fun _ => rfl
  haveI : IsScalarTower K K[X] (chartRing K ({s} : Set L)) :=
    IsScalarTower.of_algebraMap_eq fun k => ((Polynomial.aeval u).commutes k).symm
  haveI : IsScalarTower K K[X] (Localization.AtPrime 𝔪) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪),
        IsScalarTower.algebraMap_apply K[X] (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪),
        IsScalarTower.algebraMap_apply K K[X] (chartRing K ({s} : Set L))]

  haveI : Module.IsTorsionFree K[X] (chartRing K ({s} : Set L)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp hu)
  haveI : Module.Flat K[X] (chartRing K ({s} : Set L)) := inferInstance

  haveI : Algebra.FiniteType K[X] (chartRing K ({s} : Set L)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K K[X] (chartRing K ({s} : Set L))
  haveI : Algebra.FinitePresentation K[X] (chartRing K ({s} : Set L)) :=
    (Algebra.FinitePresentation.of_finiteType).mp ‹_›

  have hXp : (X : K[X]) ∈ 𝔪.under K[X] := by
    change algebraMap K[X] (chartRing K ({s} : Set L)) X ∈ 𝔪
    rwa [halg, Polynomial.aeval_X]
  haveI : (𝔪.under K[X]).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance fun h =>
      Polynomial.X_ne_zero ((Submodule.eq_bot_iff _).mp h X hXp)
  letI := Localization.AtPrime.algebraOfLiesOver (𝔪.under K[X]) 𝔪

  haveI : Module.Finite K (K[X] ⧸ 𝔪.under K[X]) :=
    finite_of_finite_type_of_isJacobsonRing K _
  haveI : Algebra.IsAlgebraic K (K[X] ⧸ 𝔪.under K[X]) := Algebra.IsAlgebraic.of_finite K _
  haveI : PerfectField (K[X] ⧸ 𝔪.under K[X]) := Algebra.IsAlgebraic.perfectField (K := K)
  haveI : Module.Finite K (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    finite_of_finite_type_of_isJacobsonRing K _
  haveI : Module.Finite (K[X] ⧸ 𝔪.under K[X]) (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    Module.Finite.of_restrictScalars_finite K _ _
  haveI : Algebra.IsAlgebraic (K[X] ⧸ 𝔪.under K[X]) (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (K[X] ⧸ 𝔪.under K[X]) (chartRing K ({s} : Set L) ⧸ 𝔪) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsUnramifiedAt K[X] 𝔪 := by
    rw [Algebra.isUnramifiedAt_iff_map_eq (p := 𝔪.under K[X])]
    refine ⟨inferInstance, le_antisymm ?_ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap,
        IsScalarTower.algebraMap_apply K[X] (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 _).mpr hf
    · rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
      have : algebraMap (chartRing K ({s} : Set L)) (Localization.AtPrime 𝔪) u =
          algebraMap K[X] (Localization.AtPrime 𝔪) X := by
        rw [IsScalarTower.algebraMap_apply K[X] (chartRing K ({s} : Set L))
          (Localization.AtPrime 𝔪), halg, Polynomial.aeval_X]
      rw [SetLike.mem_coe, this]
      exact Ideal.mem_map_of_mem _ hXp
  haveI : Algebra.IsEtaleAt K[X] 𝔪 := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat 𝔪
  haveI : Algebra.FormallySmooth K[X] (Localization.AtPrime 𝔪) := inferInstance
  exact Algebra.FormallySmooth.comp K K[X] (Localization.AtPrime 𝔪)

private theorem formallySmooth_chartRing_localization_bot' [PerfectField K] :
    FormallySmooth K (Localization.AtPrime (⊥ : Ideal ↥(chartRing K ({s} : Set L)))) := by
  let A := chartRing K ({s} : Set L)
  have heq : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
    ext x; simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsLocalization (⊥ : Ideal A).primeCompl L :=
    heq.symm ▸ (inferInstance : IsFractionRing A L)
  let e : L ≃ₐ[K] Localization.AtPrime (⊥ : Ideal A) :=
    (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl L _).restrictScalars K
  haveI : EssFiniteType (↥A) L :=
    EssFiniteType.of_isLocalization (S := L) (nonZeroDivisors (A : Type u))
  haveI : EssFiniteType K L := EssFiniteType.comp K (↥A) L
  exact FormallySmooth.of_equiv e

private theorem chartRing_isSmoothAt' [PerfectField K] (𝔭 : Ideal ↥(chartRing K ({s} : Set L)))
    [𝔭.IsPrime] : IsSmoothAt K 𝔭 := by
  rcases eq_or_ne 𝔭 ⊥ with rfl | h𝔭
  · exact formallySmooth_chartRing_localization_bot' K s
  · exact formallySmooth_chartRing_localization_closed' K s 𝔭 h𝔭

omit [FiniteDimensional ↥K⟮s⟯ L] in

private theorem rank_kaehler_eq_one_of_finite_adjoin' (hs : Transcendental K s) :
    Module.rank L Ω[L⁄K] = 1 := by
  haveI : FormallyEtale (↥K⟮s⟯) L := FormallyEtale.of_isSeparable (↥K⟮s⟯) L
  have e := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (↥K⟮s⟯) L).symm
  rw [e.rank_eq, Module.rank_baseChange, rank_kaehler_intermediateField_adjoin_single K s hs]
  simp

private theorem rank_kaehler_chartRing_localization_away_eq_one' (hs : Transcendental K s)
    (t : chartRing K ({s} : Set L)) (ht : t ≠ 0) :
    Module.rank (Localization.Away t) Ω[(Localization.Away t)⁄K] = 1 := by
  have htnzd := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away t) htnzd
  letI : Algebra (Localization.Away t) L :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away t) L
      (Submonoid.powers t) (nonZeroDivisors _) htnzd
  haveI : IsScalarTower (chartRing K ({s} : Set L)) (Localization.Away t) L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away t) L
      (Submonoid.powers t) (nonZeroDivisors _) htnzd
  haveI : IsScalarTower K (Localization.Away t) L :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply K (↥(chartRing K ({s} : Set L))) L,
        IsScalarTower.algebraMap_apply (↥(chartRing K ({s} : Set L))) (Localization.Away t) L,
        ← IsScalarTower.algebraMap_apply K (↥(chartRing K ({s} : Set L))) (Localization.Away t)]
  haveI : IsFractionRing (Localization.Away t) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers t) (Localization.Away t) L
  rw [rank_kaehler_eq_of_formallyEtale K (Localization.Away t) L (nonZeroDivisors _) le_rfl]
  exact_mod_cast rank_kaehler_eq_one_of_finite_adjoin' K s hs

private theorem formallySmooth_chartRing' [PerfectField K] :
    FormallySmooth K ↥(chartRing K ({s} : Set L)) := by
  rw [← smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  exact fun 𝔭 => chartRing_isSmoothAt' K s 𝔭.asIdeal

private theorem locally_isStandardSmoothOfRelativeDimension_one_chartRing' [PerfectField K]
    (hs : Transcendental K s) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K ↥(chartRing K ({s} : Set L))) := by
  haveI : Algebra.Smooth K (chartRing K ({s} : Set L)) :=
    { formallySmooth := formallySmooth_chartRing' K s
      finitePresentation := chartRing_finitePresentation' K s }
  obtain ⟨σ, hσ, hstd⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth K (chartRing K ({s} : Set L))
  refine ⟨σ \ {0}, by rw [Ideal.span_sdiff_singleton_zero]; exact hσ, fun t ht => ?_⟩
  obtain ⟨htσ, ht0⟩ := ht; simp only [Set.mem_singleton_iff] at ht0
  show RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap _ (Localization.Away t)).comp (algebraMap K (chartRing K ({s} : Set L))))
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  haveI := hstd t htσ
  haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_of_le_nonZeroDivisors
    (Localization.Away t) (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  exact (IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1).mpr
    (rank_kaehler_chartRing_localization_away_eq_one' K s hs t ht0)

private theorem smoothOfRelativeDimension_one_Spec_chartRing' [PerfectField K] (hs : Transcendental K s) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K ↥(chartRing K ({s} : Set L))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmoothOfRelativeDimension_one_chartRing' K s hs

end OneGenerator

private theorem smoothOfRelativeDimension_one_gluedToBase' [PerfectField K] (t : L) [Fact (t ≠ 0)]
    (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L] [Algebra.IsSeparable ↥K⟮t⟯ L]
    [FiniteDimensional ↥K⟮t⁻¹⟯ L] [Algebra.IsSeparable ↥K⟮t⁻¹⟯ L] :
    SmoothOfRelativeDimension 1 (gluedToBase K t) :=
  smoothOfRelativeDimension_one_gluedToBase_of_charts K t
    (smoothOfRelativeDimension_one_Spec_chartRing' K t ht)
    (smoothOfRelativeDimension_one_Spec_chartRing' K t⁻¹ fun h => ht (IsAlgebraic.inv_iff.mp h))

end S7A8SM
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM"

namespace S7bP

section Packaging

open IntermediateField IsDedekindDomain

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]

section OneGenerator

open scoped AlgebraicCurve.CurveModel

variable (s : L) [FiniteDimensional ↥K⟮s⟯ L] [Algebra.IsSeparable ↥K⟮s⟯ L]

open scoped IntermediateField.algebraAdjoinAdjoin in
private scoped instance isDedekindDomain_chartRing' : IsDedekindDomain ↥(CurveModel.chartRing K ({s} : Set L)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin K ({s} : Set L)) ↥K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
private scoped instance finite_chartRing' :
    Module.Finite ↥(Algebra.adjoin K ({s} : Set L)) ↥(CurveModel.chartRing K ({s} : Set L)) :=
  IsIntegralClosure.finite (Algebra.adjoin K ({s} : Set L)) ↥K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
private scoped instance isFractionRing_chartRing' : IsFractionRing ↥(CurveModel.chartRing K ({s} : Set L)) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin K ({s} : Set L)) ↥K⟮s⟯ L _

private scoped instance finiteType_chartRing' : Algebra.FiniteType K ↥(CurveModel.chartRing K ({s} : Set L)) :=
  (Algebra.FiniteType.adjoin_of_finite (R := K) (Set.finite_singleton s)).trans
    (inferInstance :
      Algebra.FiniteType ↥(Algebra.adjoin K ({s} : Set L)) ↥(CurveModel.chartRing K ({s} : Set L)))

private scoped instance isNoetherianRing_chartRing' : IsNoetherianRing ↥(CurveModel.chartRing K ({s} : Set L)) :=
  inferInstance

private theorem isMaximal_iff_ne_bot' (hs : Transcendental K s)
    (𝔭 : Ideal ↥(CurveModel.chartRing K ({s} : Set L))) [𝔭.IsPrime] : 𝔭.IsMaximal ↔ 𝔭 ≠ ⊥ :=
  ⟨fun h => Ring.ne_bot_of_isMaximal_of_not_isField h (CurveModel.not_isField_chartRing K s hs),
   fun h => Ideal.IsPrime.isMaximal inferInstance h⟩

variable {K}

private def primeOfValuationSubring' (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : HeightOneSpectrum ↥(CurveModel.chartRing K ({s} : Set L)) :=
  ⟨CurveModel.centre K s O hK hs, inferInstance, CurveModel.centre_ne_bot K s O hK hs hO⟩

private theorem valuationSubringAtPrime_le' (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring' s O hK hs hO) ≤ O := by
  intro x hx
  have hx' : ∃ (a b : ↥(CurveModel.chartRing K ({s} : Set L)))
      (_ : b ∈ (CurveModel.centre K s O hK hs).primeCompl),
      x = algebraMap _ L a * (algebraMap _ L b)⁻¹ := hx
  obtain ⟨a, b, hb, rfl⟩ := hx'
  apply O.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, show O.valuation (algebraMap _ L b) = 1 from
    CurveModel.valuation_eq_one_of_not_mem_centre K s O hK hs hb, inv_one, mul_one]
  exact CurveModel.valuation_coe_le_one K s O hK hs a

private theorem valuationSubringAtPrime_primeOfValuationSubring' (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring' s O hK hs hO) = O :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le' s O hK hs hO) hO

private theorem exists_ofHeightOneSpectrum_eq' (v : Place K L) (hs : s ∈ v.toValuationSubring) :
    ∃ 𝔭 : HeightOneSpectrum ↥(CurveModel.chartRing K ({s} : Set L)),
      Place.ofHeightOneSpectrum (K := K) 𝔭 = v := by
  refine ⟨primeOfValuationSubring' s v.toValuationSubring v.algebraMap_mem' hs v.ne_top', ?_⟩
  apply Place.ext
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact valuationSubringAtPrime_primeOfValuationSubring' s _ _ hs _

private theorem mem_ofHeightOneSpectrum' (𝔭 : HeightOneSpectrum ↥(CurveModel.chartRing K ({s} : Set L))) :
    s ∈ (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
  exact 𝔭.valuation_le_one (K := L)
    (⟨s, CurveModel.subset_chartRing K ({s} : Set L) (Set.mem_singleton s)⟩ :
      ↥(CurveModel.chartRing K ({s} : Set L)))

private theorem ofHeightOneSpectrum_injective' :
    Function.Injective
      (Place.ofHeightOneSpectrum (K := K) (F := L) (R := ↥(CurveModel.chartRing K ({s} : Set L)))) := by
  intro 𝔭 𝔮 h
  have hv := congrArg Place.toValuationSubring h
  simp only [Place.ofHeightOneSpectrum_toValuationSubring] at hv
  have hequiv := (Valuation.isEquiv_iff_valuationSubring _ _).mpr hv
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
  exact hequiv.lt_one_iff_lt_one

variable (K)

end OneGenerator
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM"

section PlaceDictionary

variable [FiniteDimensional ↥K⟮t⟯ L] [Algebra.IsSeparable ↥K⟮t⟯ L]

private scoped instance locallyOfFiniteType_gluedToBase' : LocallyOfFiniteType (CurveModel.gluedToBase K t) := by
  have h₀' : LocallyOfFiniteType (CurveModel.ι₀ K t ≫ CurveModel.gluedToBase K t) := by
    rw [CurveModel.ι₀_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (CurveModel.ιInf K t ≫ CurveModel.gluedToBase K t) := by
    rw [CurveModel.ιInf_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (span (CurveModel.f₀ K t) (CurveModel.fInf K t))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (CurveModel.f₀ K t) (CurveModel.fInf K t))).f none ≫
        CurveModel.gluedToBase K t = CurveModel.f₀ K t ≫ (CurveModel.ι₀ K t ≫ CurveModel.gluedToBase K t) := by
      show colimit.ι (span (CurveModel.f₀ K t) (CurveModel.fInf K t)) none ≫ CurveModel.gluedToBase K t = _
      rw [← colimit.w (span (CurveModel.f₀ K t) (CurveModel.fInf K t)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs
      (LocallyOfFiniteType (CurveModel.f₀ K t ≫ (CurveModel.ι₀ K t ≫ CurveModel.gluedToBase K t)))
  · change LocallyOfFiniteType (CurveModel.ι₀ K t ≫ CurveModel.gluedToBase K t)
    exact h₀'
  · change LocallyOfFiniteType (CurveModel.ιInf K t ≫ CurveModel.gluedToBase K t)
    exact hInf'

private scoped instance jacobsonSpace_glued' : JacobsonSpace (CurveModel.glued K t) :=
  LocallyOfFiniteType.jacobsonSpace (CurveModel.gluedToBase K t)

private theorem ι₀_mem_closedPoints_iff' (x : CurveModel.X₀ K t) :
    (CurveModel.ι₀ K t).base x ∈ closedPoints (CurveModel.glued K t) ↔ x ∈ closedPoints (CurveModel.X₀ K t) := by
  rw [← Set.mem_preimage, (CurveModel.ι₀ K t).isOpenEmbedding.preimage_closedPoints]

private theorem ιInf_mem_closedPoints_iff' (x : CurveModel.XInf K t) :
    (CurveModel.ιInf K t).base x ∈ closedPoints (CurveModel.glued K t) ↔
      x ∈ closedPoints (CurveModel.XInf K t) := by
  rw [← Set.mem_preimage, (CurveModel.ιInf K t).isOpenEmbedding.preimage_closedPoints]

private def primeOfι₀' (ht : Transcendental K t) (x₀ : CurveModel.X₀ K t)
    (hx : (CurveModel.ι₀ K t).base x₀ ∈ closedPoints (CurveModel.glued K t)) :
    HeightOneSpectrum ↥(CurveModel.chartRing K ({t} : Set L)) :=
  ⟨x₀.asIdeal, x₀.isPrime,
    (isMaximal_iff_ne_bot' K t ht _).mp ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mp
      ((ι₀_mem_closedPoints_iff' K t x₀).mp hx))⟩

private def primeOfιInf' (ht : Transcendental K t) (xi : CurveModel.XInf K t)
    (hx : (CurveModel.ιInf K t).base xi ∈ closedPoints (CurveModel.glued K t)) :
    HeightOneSpectrum ↥(CurveModel.chartRing K ({t⁻¹} : Set L)) :=
  ⟨xi.asIdeal, xi.isPrime,
    (isMaximal_iff_ne_bot' K t⁻¹ (CurveModel.transcendental_inv K t ht) _).mp
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mp
        ((ιInf_mem_closedPoints_iff' K t xi).mp hx))⟩

open scoped Classical in

private def gluedPlaceOfPoint' (ht : Transcendental K t) (x : closedPoints (CurveModel.glued K t)) : Place K L :=
  if h : x.1 ∈ Set.range (CurveModel.ι₀ K t).base then
    Place.ofHeightOneSpectrum (K := K)
      (primeOfι₀' K t ht (Classical.choose h) (by rw [Classical.choose_spec h]; exact x.2))
  else
    Place.ofHeightOneSpectrum (K := K)
      (primeOfιInf' K t ht (Classical.choose (CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h))
        (by rw [Classical.choose_spec (CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h)]; exact x.2))

private theorem gluedPlaceOfPoint'_ι₀ (ht : Transcendental K t) (x₀ : CurveModel.X₀ K t)
    (hx : (CurveModel.ι₀ K t).base x₀ ∈ closedPoints (CurveModel.glued K t)) :
    gluedPlaceOfPoint' K t ht ⟨(CurveModel.ι₀ K t).base x₀, hx⟩ =
      Place.ofHeightOneSpectrum (K := K) (primeOfι₀' K t ht x₀ hx) := by
  have h : (CurveModel.ι₀ K t).base x₀ ∈ Set.range (CurveModel.ι₀ K t).base := ⟨x₀, rfl⟩
  have hc : Classical.choose h = x₀ :=
    (CurveModel.ι₀ K t).isOpenEmbedding.injective (Classical.choose_spec h)
  have key : ∀ (y : CurveModel.X₀ K t) (hy) (_ : y = x₀),
      primeOfι₀' K t ht y hy = primeOfι₀' K t ht x₀ hx := by
    rintro y hy rfl; rfl
  unfold gluedPlaceOfPoint'
  rw [dif_pos h, key _ _ hc]

private theorem gluedPlaceOfPoint'_of_not_mem (ht : Transcendental K t) (x : closedPoints (CurveModel.glued K t))
    (h : x.1 ∉ Set.range (CurveModel.ι₀ K t).base) (xi : CurveModel.XInf K t)
    (hxi : (CurveModel.ιInf K t).base xi = x.1) :
    gluedPlaceOfPoint' K t ht x =
      Place.ofHeightOneSpectrum (K := K) (primeOfιInf' K t ht xi (by rw [hxi]; exact x.2)) := by
  have hc : Classical.choose (CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h) = xi :=
    (CurveModel.ιInf K t).isOpenEmbedding.injective
      ((Classical.choose_spec (CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h)).trans hxi.symm)
  have key : ∀ (y : CurveModel.XInf K t) (hy) (_ : y = xi),
      primeOfιInf' K t ht y hy = primeOfιInf' K t ht xi (by rw [hxi]; exact x.2) := by
    rintro y hy rfl; rfl
  unfold gluedPlaceOfPoint'
  rw [dif_neg h, key _ _ hc]

private theorem t_mem_of_ι₀' (ht : Transcendental K t) (x₀ : CurveModel.X₀ K t) (hx) :
    t ∈ (Place.ofHeightOneSpectrum (K := K) (primeOfι₀' K t ht x₀ hx)).toValuationSubring :=
  mem_ofHeightOneSpectrum' t _

private theorem t_not_mem_of_ιInf' (ht : Transcendental K t) (xi : CurveModel.XInf K t) (hx)
    (hxi : CurveModel.tInvChart K t ∈ xi.asIdeal) :
    t ∉ (Place.ofHeightOneSpectrum (K := K) (primeOfιInf' K t ht xi hx)).toValuationSubring := by
  intro htmem
  set 𝔮 := primeOfιInf' K t ht xi hx
  have h1 : 𝔮.valuation L ((CurveModel.tInvChart K t : ↥(CurveModel.chartRing K ({t⁻¹} : Set L))) : L) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮 (CurveModel.tInvChart K t)).mpr hxi
  have h2 : 𝔮.valuation L t ≤ 1 := by
    rwa [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
      at htmem
  have h3 : 𝔮.valuation L (t * t⁻¹) < 1 := by
    rw [map_mul]
    calc 𝔮.valuation L t * 𝔮.valuation L t⁻¹
        ≤ 1 * 𝔮.valuation L t⁻¹ := mul_le_mul' h2 le_rfl
      _ = 𝔮.valuation L ((CurveModel.tInvChart K t : ↥(CurveModel.chartRing K ({t⁻¹} : Set L))) : L) := by
          rw [one_mul, CurveModel.coe_tInvChart]
      _ < 1 := h1
  rw [mul_inv_cancel₀ (Fact.out : t ≠ 0), map_one] at h3
  exact lt_irrefl _ h3

private theorem gluedPlaceOfPoint'_injective (ht : Transcendental K t) :
    Function.Injective (gluedPlaceOfPoint' K t ht) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  by_cases h₁ : x ∈ Set.range (CurveModel.ι₀ K t).base <;>
    by_cases h₂ : y ∈ Set.range (CurveModel.ι₀ K t).base
  · obtain ⟨x₀, rfl⟩ := h₁
    obtain ⟨y₀, rfl⟩ := h₂
    rw [gluedPlaceOfPoint'_ι₀, gluedPlaceOfPoint'_ι₀] at hxy
    have h' := ofHeightOneSpectrum_injective' t hxy
    have hxy' : x₀ = y₀ := PrimeSpectrum.ext (congrArg HeightOneSpectrum.asIdeal h')
    subst hxy'
    rfl
  · exfalso
    obtain ⟨x₀, rfl⟩ := h₁
    obtain ⟨yi, hyi⟩ := CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h₂
    rw [gluedPlaceOfPoint'_ι₀, gluedPlaceOfPoint'_of_not_mem K t ht ⟨y, hy⟩ h₂ yi hyi] at hxy
    refine t_not_mem_of_ιInf' K t ht yi _ (CurveModel.tInvChart_mem_of_not_mem_range K t yi ?_)
      (hxy ▸ t_mem_of_ι₀' K t ht x₀ hx)
    rwa [hyi]
  · exfalso
    obtain ⟨y₀, rfl⟩ := h₂
    obtain ⟨xi, hxi⟩ := CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h₁
    rw [gluedPlaceOfPoint'_ι₀, gluedPlaceOfPoint'_of_not_mem K t ht ⟨x, hx⟩ h₁ xi hxi] at hxy
    refine t_not_mem_of_ιInf' K t ht xi _ (CurveModel.tInvChart_mem_of_not_mem_range K t xi ?_)
      (hxy ▸ t_mem_of_ι₀' K t ht y₀ hy)
    rwa [hxi]
  · obtain ⟨xi, hxi⟩ := CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h₁
    obtain ⟨yi, hyi⟩ := CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h₂
    rw [gluedPlaceOfPoint'_of_not_mem K t ht ⟨x, hx⟩ h₁ xi hxi,
      gluedPlaceOfPoint'_of_not_mem K t ht ⟨y, hy⟩ h₂ yi hyi] at hxy
    have h' := ofHeightOneSpectrum_injective' t⁻¹ hxy
    have hxy' : xi = yi := PrimeSpectrum.ext (congrArg HeightOneSpectrum.asIdeal h')
    subst hxy'
    exact Subtype.ext (hxi.symm.trans hyi)

private theorem gluedPlaceOfPoint'_surjective (ht : Transcendental K t) :
    Function.Surjective (gluedPlaceOfPoint' K t ht) := by
  intro v
  by_cases hv : t ∈ v.toValuationSubring
  · obtain ⟨𝔭, h𝔭⟩ := exists_ofHeightOneSpectrum_eq' t v hv
    let x₀ : CurveModel.X₀ K t := ⟨𝔭.asIdeal, 𝔭.isPrime⟩
    have hx₀ : x₀ ∈ closedPoints (CurveModel.X₀ K t) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mpr 𝔭.isMaximal
    refine ⟨⟨(CurveModel.ι₀ K t).base x₀, (ι₀_mem_closedPoints_iff' K t x₀).mpr hx₀⟩, ?_⟩
    rw [gluedPlaceOfPoint'_ι₀, ← h𝔭]
    rfl
  · have hv' : t⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem t).resolve_left hv
    obtain ⟨𝔮, h𝔮⟩ := exists_ofHeightOneSpectrum_eq' t⁻¹ v hv'
    let xi : CurveModel.XInf K t := ⟨𝔮.asIdeal, 𝔮.isPrime⟩
    have hxi : xi ∈ closedPoints (CurveModel.XInf K t) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mpr 𝔮.isMaximal
    have hmem : CurveModel.tInvChart K t ∈ xi.asIdeal := by
      change CurveModel.tInvChart K t ∈ 𝔮.asIdeal
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
      have hvt : ¬ 𝔮.valuation L t ≤ 1 := by
        rwa [← Valuation.mem_valuationSubring_iff,
          ← Place.ofHeightOneSpectrum_toValuationSubring (K := K) 𝔮, h𝔮]
      have hprod : 𝔮.valuation L ((CurveModel.tInvChart K t : ↥(CurveModel.chartRing K ({t⁻¹} : Set L))) : L) *
          𝔮.valuation L t = 1 := by
        rw [← map_mul, CurveModel.coe_tInvChart, inv_mul_cancel₀ (Fact.out : t ≠ 0), map_one]
      by_contra hge
      have hge' : 1 ≤ 𝔮.valuation L ((CurveModel.tInvChart K t : ↥(CurveModel.chartRing K ({t⁻¹} : Set L))) : L) :=
        not_lt.mp hge
      have : (1 : WithZero (Multiplicative ℤ)) < 1 :=
        calc (1 : WithZero (Multiplicative ℤ)) < 𝔮.valuation L t := not_le.mp hvt
          _ = 1 * 𝔮.valuation L t := (one_mul _).symm
          _ ≤ 𝔮.valuation L ((CurveModel.tInvChart K t : ↥(CurveModel.chartRing K ({t⁻¹} : Set L))) : L) *
                𝔮.valuation L t := mul_le_mul' hge' le_rfl
          _ = 1 := hprod
      exact lt_irrefl _ this
    have hnot : (CurveModel.ιInf K t).base xi ∉ Set.range (CurveModel.ι₀ K t).base :=
      fun hr => ((CurveModel.ιInf_mem_range_ι₀_iff K t xi).mp hr) hmem
    refine ⟨⟨(CurveModel.ιInf K t).base xi, (ιInf_mem_closedPoints_iff' K t xi).mpr hxi⟩, ?_⟩
    rw [gluedPlaceOfPoint'_of_not_mem K t ht _ hnot xi rfl, ← h𝔮]
    rfl

private theorem gluedPlaceOfPoint'_bijective (ht : Transcendental K t) :
    Function.Bijective (gluedPlaceOfPoint' K t ht) :=
  ⟨gluedPlaceOfPoint'_injective K t ht, gluedPlaceOfPoint'_surjective K t ht⟩

private theorem range_stalk_eq_gluedPlaceOfPoint' (ht : Transcendental K t) (x : closedPoints (CurveModel.glued K t)) :
    (((CurveModel.gluedFunctionFieldEquiv K t).symm : (CurveModel.glued K t).functionField ≃+* L).toRingHom.comp
        (algebraMap ((CurveModel.glued K t).presheaf.stalk x.1) (CurveModel.glued K t).functionField)).range =
      (gluedPlaceOfPoint' K t ht x).toValuationSubring.toSubring := by
  obtain ⟨x, hx⟩ := x
  by_cases h : x ∈ Set.range (CurveModel.ι₀ K t).base
  · obtain ⟨x₀, rfl⟩ := h
    rw [gluedPlaceOfPoint'_ι₀, Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := L) (v := primeOfι₀' K t ht x₀ hx),
      HeightOneSpectrum.valuationSubringAtPrime_toSubring]
    apply SetLike.ext'
    erw [CurveModel.range_ffEquiv_symm_comp_algebraMap_stalk K t (CurveModel.chartRing K ({t} : Set L))
      (CurveModel.incl₀ K t) (fun a => CurveModel.coe_chartIncl K _ a) (CurveModel.ι₀ K t) rfl x₀]
    ext y
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
  · obtain ⟨xi, rfl⟩ := CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K t h
    rw [gluedPlaceOfPoint'_of_not_mem K t ht _ h xi rfl,
      Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := L) (v := primeOfιInf' K t ht xi hx),
      HeightOneSpectrum.valuationSubringAtPrime_toSubring]
    apply SetLike.ext'
    erw [CurveModel.range_ffEquiv_symm_comp_algebraMap_stalk K t (CurveModel.chartRing K ({t⁻¹} : Set L))
      (CurveModel.inclInf K t) (fun a => CurveModel.coe_chartIncl K _ a) (CurveModel.ιInf K t)
      (CurveModel.glue_condition K t).symm xi]
    ext y
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩

private theorem exists_placeOfPoint_glued (ht : Transcendental K t) :
    ∃ P : closedPoints (CurveModel.glued K t) → Place K L, Function.Bijective P ∧
      ∀ x : closedPoints (CurveModel.glued K t),
        (((CurveModel.gluedFunctionFieldEquiv K t).symm :
              (CurveModel.glued K t).functionField ≃+* L).toRingHom.comp
            (algebraMap ((CurveModel.glued K t).presheaf.stalk x.1)
              (CurveModel.glued K t).functionField)).range =
          (P x).toValuationSubring.toSubring :=
  ⟨gluedPlaceOfPoint' K t ht, gluedPlaceOfPoint'_bijective K t ht, range_stalk_eq_gluedPlaceOfPoint' K t ht⟩

end PlaceDictionary
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM"

private theorem finset_subset_affineOpen_glued_of_infinite [Infinite K] [FiniteDimensional ↥K⟮t⟯ L] :
    ∀ F : Finset (CurveModel.glued K t), ∃ U : (CurveModel.glued K t).Opens,
      IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  intro F
  have hfin : ((⋃ x ∈ (F : Set (CurveModel.glued K t)), {a : K | x ∉ CurveModel.Ua K t a}) ∪
      {a : K | t - algebraMap K L a = 0}).Finite := by
    refine (F.finite_toSet.biUnion fun x _ => CurveModel.finite_setOf_not_mem_Ua K t x).union ?_
    refine Set.Subsingleton.finite fun a ha' b hb' => ?_
    apply (algebraMap K L).injective
    have ha'' : t - algebraMap K L a = 0 := ha'
    have hb'' : t - algebraMap K L b = 0 := hb'
    rw [sub_eq_zero] at ha'' hb''
    rw [← ha'', ← hb'']
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  refine ⟨CurveModel.Ua K t a, CurveModel.isAffineOpen_Ua K t a (fun h => ha (Or.inr h)), fun x hx => ?_⟩
  by_contra h
  exact ha (Or.inl (Set.mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, h⟩))

end Packaging
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM"

end S7bP
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP"

theorem solution (K : Type u) [Field K] [Infinite K]
    [PerfectField K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L] [Algebra.IsSeparable ↥K⟮t⟯ L] :
    IsProper (gluedToBase K t) ∧
    SmoothOfRelativeDimension 1 (gluedToBase K t) ∧
    (∃ P : closedPoints (glued K t) → Place K L, Function.Bijective P ∧
      ∀ x : closedPoints (glued K t),
        (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
            (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
          (P x).toValuationSubring.toSubring) ∧
    (∀ F : Finset (glued K t), ∃ U : (glued K t).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :=
  ⟨isProper_gluedToBase_of_isSeparable K t,
    (haveI := finiteDimensional_adjoin_inv K t; haveI := isSeparable_adjoin_inv K t;
      S7A8SM.smoothOfRelativeDimension_one_gluedToBase' K t ht),
    ⟨S7bP.gluedPlaceOfPoint' K t ht, S7bP.gluedPlaceOfPoint'_bijective K t ht,
      S7bP.range_stalk_eq_gluedPlaceOfPoint' K t ht⟩,
    S7bP.finset_subset_affineOpen_glued_of_infinite K t⟩

end
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP"

end S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued (solution)
