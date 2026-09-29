-- Prove2me | Definitions.Def_AlgebraicCurve_CurveModelSmooth
-- name    : AlgebraicCurve_CurveModelSmooth
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/64af324c-cdda-5f83-9c83-941d37c1021d
-- title:
--   Smoothness of the one-generator chart algebra over the base field
-- statement:
--   Fix a field $K$ of characteristic zero, an extension field $L$ of $K$, and an element $s\in L$ transcendental over $K$ with $L$ finite over $K\langle s\rangle$. The chart algebra $A=\mathrm{chartRing}\,K\,\{s\}$ is the integral closure in $L$ of $K[s]=\mathrm{adjoin}\,K\,\{s\}$, i.e. the subalgebra of elements of $L$ integral over $K[s]$; the module establishes that $\mathrm{Spec}\,A\to\mathrm{Spec}\,K$ is smooth of relative dimension one. The single definition is `freeSubmersivePresentation`, which equips the polynomial algebra $\mathrm{MvPolynomial}\,\iota\,R$ over a commutative ring $R$ with the structure of a submersive presentation having generators indexed by $\iota$, an empty family of relations, and unit Jacobian; from it follow standard smoothness of relative dimension one for $R[X]$ and smoothness of relative dimension one for $\mathrm{Spec}$ of $K\to K[X]$. The remaining declarations are the steps of the proof: for a Dedekind domain $A$ over $K$ and a nonzero prime $\mathfrak m$, an element $u\in\mathfrak m\setminus\{0\}$ whose image generates the maximal ideal of $A_{\mathfrak m}$; transcendence over $K$ of any nonzero element of a proper ideal of a domain containing $K$; finite presentation of $A$ over $K$; formal smoothness of $A_{\mathfrak p}$ over $K$ for $\mathfrak p$ a nonzero prime (through unramifiedness, hence étaleness, of $A_{\mathfrak p}$ over $K[X]$ sent to a uniformiser) and at $\mathfrak p=\bot$, where the localisation is the fraction field $L$; invariance of the rank of Kähler differentials under localisation at a submonoid of nonzerodivisors; $\mathrm{rank}_{K\langle s\rangle}\Omega_{K\langle s\rangle/K}=\mathrm{rank}_L\Omega_{L/K}=1$ and the same for localisations $A_t$ with $t\neq0$; formal smoothness of $A$ over $K$; and, finally, that $K\to A$ is locally standard smooth of relative dimension one, whence the assertion about $\mathrm{Spec}$.
--
--   **Relation to Mathlib.** The notions used (`SubmersivePresentation`, `IsStandardSmoothOfRelativeDimension`, `RingHom.Locally`, `SmoothOfRelativeDimension`, `IsSmoothAt`/`smoothLocus`, `FormallySmooth`, Kähler differentials) are Mathlib's; the module adds the submersive presentation of a polynomial algebra with empty relation family and the resulting smoothness results for the project's `chartRing`.
--
--   **Where it is used.** The curve-model structure requires its structure morphism to the base to be smooth of relative dimension one; the results here supply that property for the affine charts built from a single transcendental generator of a function field, so that a smooth projective model can be assembled from the chart algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModelSmooth.lean

import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_JacJ1_ChartAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial MvPolynomial Algebra IntermediateField IsLocalRing
open IntermediateField.algebraAdjoinAdjoin TensorProduct

universe u

namespace AlgebraicCurve.CurveModel

noncomputable def freeSubmersivePresentation (R : Type u) [CommRing R] (ι : Type) :
    SubmersivePresentation R (MvPolynomial ι R) ι (PEmpty : Type) where
  __ := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by simp [Set.range_eq_empty, Generators.ker_mvPolynomial]
  map := PEmpty.elim
  map_inj := fun a => a.elim
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian, LinearMap.det_eq_one_of_subsingleton, map_one]
    exact isUnit_one

scoped instance isStandardSmoothOfRelativeDimension_polynomial (R : Type u) [CommRing R] :
    IsStandardSmoothOfRelativeDimension 1 R R[X] := by
  have h : IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial PUnit R) :=
    (freeSubmersivePresentation R PUnit).isStandardSmoothOfRelativeDimension
      (by simp [Presentation.dimension])
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1) (R := R)
    (S := MvPolynomial PUnit R) (MvPolynomial.uniqueAlgEquiv R PUnit)

variable (K : Type u) [Field K]

theorem smoothOfRelativeDimension_one_Spec_polynomial :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K K[X]))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    (algebraMap K K[X])
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
      (isStandardSmoothOfRelativeDimension_polynomial K))

variable {L : Type u} [Field L] [Algebra K L]

section Coordinate

variable {A : Type u} [CommRing A] [IsDedekindDomain A] [Algebra K A]

theorem exists_mem_and_maximalIdeal_eq_span (𝔪 : Ideal A) [𝔪.IsPrime] (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ u : A, u ∈ 𝔪 ∧ u ≠ 0 ∧
      maximalIdeal (Localization.AtPrime 𝔪) =
        Ideal.span {algebraMap A (Localization.AtPrime 𝔪) u} := by
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A h𝔪
    (Localization.AtPrime 𝔪)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔪)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj 𝔪.primeCompl ϖ
  have hbu : IsUnit (algebraMap A (Localization.AtPrime 𝔪) (b : A)) := IsLocalization.map_units _ b
  have hirr : Irreducible (algebraMap A (Localization.AtPrime 𝔪) a) := by
    rw [← hab]
    exact (irreducible_mul_isUnit hbu).mpr hϖ
  refine ⟨a, ?_, ?_, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a).mp
      ((mem_maximalIdeal _).mpr hirr.not_isUnit)
  · rintro rfl
    exact hirr.ne_zero (map_zero _)

variable [IsDomain A] in
omit [IsDedekindDomain A] in

theorem transcendental_of_mem {𝔪 : Ideal A} (hne : 𝔪 ≠ ⊤) {u : A} (hu : u ∈ 𝔪) (h0 : u ≠ 0) :
    Transcendental K u := by
  intro halg
  have hint : IsIntegral K u := halg.isIntegral
  have hc : (minpoly K u).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint h0
  have h := minpoly.aeval K u
  rw [← (minpoly K u).X_mul_divX_add, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
  have key : algebraMap K A ((minpoly K u).coeff 0) =
      -(u * Polynomial.aeval u (minpoly K u).divX) :=
    eq_neg_of_add_eq_zero_right h
  exact hne (𝔪.eq_top_of_isUnit_mem (key ▸ 𝔪.neg_mem (𝔪.mul_mem_right _ hu))
    ((IsUnit.mk0 _ hc).map _))

end Coordinate

instance chartRing_finitePresentation [CharZero K] (s : L) [FiniteDimensional K⟮s⟯ L] :
    FinitePresentation K (chartRing K ({s} : Set L)) :=
  (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance

attribute [local instance] Ideal.Quotient.field

theorem formallySmooth_chartRing_localization_closed [CharZero K]
    (s : L) [FiniteDimensional K⟮s⟯ L] (hs : Transcendental K s)
    (𝔪 : Ideal (chartRing K ({s} : Set L))) [𝔪.IsPrime] (h𝔪 : 𝔪 ≠ ⊥) :
    Algebra.FormallySmooth K (Localization.AtPrime 𝔪) := by
  have _ := hs
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
  haveI : CharZero (K[X] ⧸ 𝔪.under K[X]) :=
    charZero_of_injective_algebraMap (algebraMap K (K[X] ⧸ 𝔪.under K[X])).injective
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

theorem formallySmooth_chartRing_localization_bot [CharZero K]
    (s : L) [FiniteDimensional K⟮s⟯ L] :
    FormallySmooth K (Localization.AtPrime (⊥ : Ideal (chartRing K ({s} : Set L)))) := by
  let A := chartRing K ({s} : Set L)

  have heq : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
    ext x; simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsLocalization (⊥ : Ideal A).primeCompl L :=
    heq.symm ▸ (inferInstance : IsFractionRing A L)
  let e : L ≃ₐ[K] Localization.AtPrime (⊥ : Ideal A) :=
    (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl L _).restrictScalars K
  haveI : PerfectField K := .ofCharZero
  haveI : EssFiniteType (↥A) L :=
    EssFiniteType.of_isLocalization (S := L) (nonZeroDivisors (A : Type u))
  haveI : EssFiniteType K L := EssFiniteType.comp K (↥A) L
  exact FormallySmooth.of_equiv e

theorem chartRing_isSmoothAt [CharZero K] (s : L) [FiniteDimensional K⟮s⟯ L]
    (hs : Transcendental K s) (𝔭 : Ideal (chartRing K ({s} : Set L))) [𝔭.IsPrime] :
    IsSmoothAt K 𝔭 := by
  rcases eq_or_ne 𝔭 ⊥ with rfl | h𝔭
  · exact formallySmooth_chartRing_localization_bot K s
  · exact formallySmooth_chartRing_localization_closed K s hs 𝔭 h𝔭

theorem isStandardSmoothOfRelativeDimension_adjoin_single (s : L) (hs : Transcendental K s) :
    IsStandardSmoothOfRelativeDimension 1 K (Algebra.adjoin K {s}) := by
  have e : K[X] ≃ₐ[K] Algebra.adjoin K ({s} : Set L) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := K) s)
      (transcendental_iff_injective.mp hs)).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval K s).symm)
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv 1 e

theorem rank_kaehler_eq_of_formallyEtale (B C : Type u) [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] [Algebra B C] [IsScalarTower K B C]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M C] :
    Module.rank B Ω[B⁄K] = Module.rank C Ω[C⁄K] := by
  haveI : FormallyEtale B C := FormallyEtale.of_isLocalization (Rₘ := C) M
  haveI : IsLocalizedModule M ((KaehlerDifferential.map K K B C).restrictScalars B) :=
    (isLocalizedModule_iff_isBaseChange M C _).mpr
      (KaehlerDifferential.isBaseChange_of_formallyEtale K B C)
  rw [← IsLocalizedModule.rank_eq M hM ((KaehlerDifferential.map K K B C).restrictScalars B)]
  exact (IsLocalization.rank_eq C M hM).symm

theorem rank_kaehler_intermediateField_adjoin_single (s : L) (hs : Transcendental K s) :
    Module.rank K⟮s⟯ Ω[K⟮s⟯⁄K] = 1 := by
  haveI := isStandardSmoothOfRelativeDimension_adjoin_single K s hs
  have h1 : Module.rank (Algebra.adjoin K ({s} : Set L)) Ω[(Algebra.adjoin K ({s} : Set L))⁄K]
      = 1 := IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
  rw [← rank_kaehler_eq_of_formallyEtale K (Algebra.adjoin K ({s} : Set L)) (↥K⟮s⟯)
    (nonZeroDivisors _) le_rfl]
  exact_mod_cast h1

theorem rank_kaehler_eq_one_of_finite_adjoin [CharZero K]
    (s : L) (hs : Transcendental K s) [FiniteDimensional K⟮s⟯ L] :
    Module.rank L Ω[L⁄K] = 1 := by
  haveI : CharZero K⟮s⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮s⟯).injective
  haveI : Algebra.IsSeparable K⟮s⟯ L := Algebra.IsSeparable.of_integral K⟮s⟯ L
  haveI : FormallyEtale (↥K⟮s⟯) L := FormallyEtale.of_isSeparable (↥K⟮s⟯) L
  have e := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (↥K⟮s⟯) L).symm
  rw [e.rank_eq, Module.rank_baseChange, rank_kaehler_intermediateField_adjoin_single K s hs]
  simp

theorem rank_kaehler_chartRing_localization_away_eq_one [CharZero K]
    (s : L) [FiniteDimensional K⟮s⟯ L] (hs : Transcendental K s)
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
  exact_mod_cast rank_kaehler_eq_one_of_finite_adjoin K s hs

theorem formallySmooth_chartRing [CharZero K]
    (s : L) [FiniteDimensional K⟮s⟯ L] (hs : Transcendental K s) :
    FormallySmooth K (chartRing K ({s} : Set L)) := by
  rw [← smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  exact fun 𝔭 => chartRing_isSmoothAt K s hs 𝔭.asIdeal

theorem locally_isStandardSmoothOfRelativeDimension_one_chartRing [CharZero K]
    (s : L) [FiniteDimensional K⟮s⟯ L] (hs : Transcendental K s) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (chartRing K ({s} : Set L))) := by
  haveI : Algebra.Smooth K (chartRing K ({s} : Set L)) :=
    { formallySmooth := formallySmooth_chartRing K s hs
      finitePresentation := chartRing_finitePresentation K s }
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
    (rank_kaehler_chartRing_localization_away_eq_one K s hs t ht0)

theorem smoothOfRelativeDimension_one_Spec_chartRing [CharZero K]
    (s : L) [FiniteDimensional K⟮s⟯ L] (hs : Transcendental K s) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({s} : Set L))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmoothOfRelativeDimension_one_chartRing K s hs

end AlgebraicCurve.CurveModel

end


