-- Prove2me | solution 1 for AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_over_algClosed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-16T10:11:08.212317+00:00
-- url     : https://prove2.me/submissions/7993031c-eb12-4801-aaa7-44aefe4683c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
import Definitions.Def_P2M_Util
import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Theorems.Thm_AlgebraicGeometry_exists_dominant_projective_formal_powerSeries_cover
import Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_IsRegularLocalRing_isDomain

universe u v

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponPowerSeriesRegularity

/-- A power series variable preserves regularity of a Noetherian local ring. -/
theorem powerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (PowerSeries R) := by
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries R) := by
    change ¬ IsUnit (PowerSeries.X : PowerSeries R)
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hgen := PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem hX
  have hmap : (maximalIdeal (PowerSeries R)).map (PowerSeries.constantCoeff : PowerSeries R →+* R) =
      maximalIdeal R := map_maximalIdeal_of_surjective (R := PowerSeries R) (S := R)
        (PowerSeries.constantCoeff (R := R)) PowerSeries.constantCoeff_surj
  rw [hmap] at hgen
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (PowerSeries R)
  calc ((maximalIdeal (PowerSeries R)).spanFinrank : WithBot ℕ∞)
      ≤ (((maximalIdeal R).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hgen
    _ = ringKrullDim R + 1 := by
      push_cast
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    _ ≤ ringKrullDim (PowerSeries R) := ringKrullDim_succ_le_ringKrullDim_powerseries

theorem fin (R : Type*) [CommRing R] [IsRegularLocalRing R] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
      exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
      letI := ih
      letI := powerSeries (MvPowerSeries (Fin n) R)
      exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

/-- The formal regular local models needed for completed nodal charts. -/
theorem mvPowerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (σ : Type*) [Finite σ] : IsRegularLocalRing (MvPowerSeries σ R) := by
  classical
  letI := Fintype.ofFinite σ
  letI := fin R (Fintype.card σ)
  exact IsRegularLocalRing.of_ringEquiv
    (MvPowerSeries.renameEquiv R (Fintype.equivFin σ)).toRingEquiv.symm

end PhilipponPowerSeriesRegularity

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.NoetherianCompletion

open scoped Topology

variable {R : Type*} [CommRing R]

theorem exists_powerSeriesMap (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ R →+* AdicCompletion I R,
      (∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  letI : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hI
  have hcomplete : CompleteSpace S ∧ T2Space S :=
    (IsAdic.isAdicComplete_iff (I := J) rfl).mp inferInstance
  letI : CompleteSpace S := hcomplete.1
  letI : T2Space S := hcomplete.2
  have hcont : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval (fun i => algebraMap R S (a i)) := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_map_of_mem _ (ha i))
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro r
    simp [MvPowerSeries.coe_eval₂Hom, S]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom, S]

theorem powerSeriesMap_surjective (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R)
    (ha : Ideal.span (Set.range a) = I)
    (f : MvPowerSeries σ R →+* AdicCompletion I R)
    (hC : ∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) :
    Function.Surjective f := by
  let S := AdicCompletion I R
  let J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = I.map (algebraMap R S) := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hX]
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, S] using
      congrArg (Ideal.map (algebraMap R S)) ha
  letI : IsAdicComplete (I.map (algebraMap R S)) S :=
    AdicCompletion.isAdicComplete_self I hI
  letI : IsHausdorff (J.map f) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C r)) =
    Ideal.Quotient.mk (J.map f) y
  rw [hC, Ideal.Quotient.eq, hmap]
  change algebraMap R (AdicCompletion I R) r - y ∈
    I.map (algebraMap R (AdicCompletion I R))
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (I := I) hI]
  change AdicCompletion.evalOneₐ I (algebraMap R S r - y) = 0
  rw [map_sub]
  change Ideal.Quotient.mk I r - AdicCompletion.evalOneₐ I y = 0
  rw [hr, sub_self]

theorem isNoetherianRing_completion [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  have hmem : ∀ i, a i ∈ I := fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨f, hC, hX⟩ := exists_powerSeriesMap I I.fg_of_isNoetherianRing a hmem
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) R) (AdicCompletion I R) f
    (powerSeriesMap_surjective I I.fg_of_isNoetherianRing a ha f hC hX)

end PhilipponMultiplicity.NoetherianCompletion

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompletionRegularity

/-- A flat local map with field closed fiber preserves local dimension. -/
theorem dimension_eq_of_flat_local_map
    (R S : Type*) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    ringKrullDim S = ringKrullDim R := by
  haveI : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := R) (S := S) (maximalIdeal R) (maximalIdeal S)
  rw [hmap, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← maximalIdeal_height_eq_ringKrullDim (R := S),
    ← maximalIdeal_height_eq_ringKrullDim (R := R)]
  exact_mod_cast h

/-- Completion at the maximal ideal preserves Krull dimension. -/
theorem dimension_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  haveI := PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
    (maximalIdeal R)
  exact dimension_eq_of_flat_local_map R _ AdicCompletion.maximalIdeal_eq_map.symm

/-- Regularity can be checked on the actual maximal-adic completion. -/
theorem regular_iff
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsRegularLocalRing R ↔ IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  haveI := PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
    (maximalIdeal R)
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff,
    AdicCompletion.spanFinrank_maximalIdeal_eq, dimension_eq]

end PhilipponCompletionRegularity

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing
namespace PhilipponRegularLocalPerfectSmooth

open Polynomial TensorProduct

theorem isUnit_add_of_mem {S : Type u} [CommRing S] [IsLocalRing S] {a b : S}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal S) : IsUnit (a + b) := by
  by_contra h
  have hab : a + b ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : a ∈ maximalIdeal S := by simpa using sub_mem hab hb
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

theorem isUnit_aeval_of_coeff_zero_ne_zero {k : Type u} [Field k] {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra k S] {t : S} (ht : t ∈ maximalIdeal S) {q : k[X]} (hq : q.coeff 0 ≠ 0) :
    IsUnit (aeval t q) := by
  have h : aeval t q = algebraMap k S (q.coeff 0) + t * aeval t q.divX := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    simp only [map_add, map_mul, aeval_X, aeval_C]
    ring
  rw [h]
  exact isUnit_add_of_mem ((IsUnit.mk0 _ hq).map _) (Ideal.mul_mem_right _ _ ht)

theorem exists_mem_notMem_sq {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (h : maximalIdeal S ≠ ⊥) : ∃ t ∈ maximalIdeal S, t ∉ (maximalIdeal S) ^ 2 := by
  by_contra hall
  push_neg at hall
  apply h
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S) (IsNoetherian.noetherian _)
  · intro x hx
    have := hall x hx
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  · exact IsLocalRing.maximalIdeal_le_jacobson _

theorem spanFinrank_maximalIdeal_quotient_congr {S : Type u} [CommRing S] {I J : Ideal S} (h : I = J)
    [hI : IsLocalRing (S ⧸ I)] [hJ : IsLocalRing (S ⧸ J)] :
    (maximalIdeal (S ⧸ I)).spanFinrank = (maximalIdeal (S ⧸ J)).spanFinrank := by
  subst h
  rfl

theorem main (n : ℕ) : ∀ (k : Type u) [Field k] [PerfectField k] (S : Type u) [CommRing S] [IsRegularLocalRing S]
    [Algebra k S] [Algebra.EssFiniteType k S],
    (maximalIdeal S).spanFinrank = n →
    Algebra.FormallySmooth k S := by
  induction n with
  | zero =>
    intro k _ _ S _ _ _ _ h0
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0
    letI : Field S := ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot).toField
    exact Algebra.FormallySmooth.of_perfectField
  | succ n ih =>
    intro k _ _ S _ _ _ _ hn
    classical
    haveI : IsDomain S := IsRegularLocalRing.isDomain S
    have hne : maximalIdeal S ≠ ⊥ := fun h => by
      rw [(Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mpr h] at hn
      exact Nat.succ_ne_zero n hn.symm
    obtain ⟨t, ht, ht2⟩ := exists_mem_notMem_sq hne
    have ht0 : t ≠ 0 := fun h => ht2 (h ▸ zero_mem _)

    have htr : Function.Injective (aeval (R := k) t) := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra hp0
      obtain ⟨q, hq, hdvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
      have hq0 : q.coeff 0 ≠ 0 := by
        rw [map_zero, sub_zero, Polynomial.X_dvd_iff] at hdvd
        exact hdvd
      have hu : IsUnit (aeval t q) := isUnit_aeval_of_coeff_zero_ne_zero ht hq0
      have h1 : t ^ (rootMultiplicity 0 p) * aeval t q = 0 := by
        have h2 := congrArg (aeval t) hq
        rw [hp, map_mul, map_pow, map_sub, aeval_X, map_zero, map_zero, sub_zero] at h2
        exact h2.symm
      have htm : t ^ (rootMultiplicity 0 p) = 0 := hu.mul_left_eq_zero.mp h1
      by_cases hm : rootMultiplicity 0 p = 0
      · rw [hm, pow_zero] at htm
        exact one_ne_zero htm
      · exact ht0 ((pow_eq_zero_iff hm).mp htm)

    haveI hprime : (Ideal.span {(X : k[X])}).IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
    let K₁ : Type u := Localization.AtPrime (Ideal.span {(X : k[X])})
    haveI : IsDiscreteValuationRing K₁ :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X]
        (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_ne_zero) K₁
    have hunits : ∀ y : (Ideal.span {(X : k[X])}).primeCompl, IsUnit (aeval t (y : k[X])) := by
      rintro ⟨y, hy⟩
      apply isUnit_aeval_of_coeff_zero_ne_zero ht
      intro h0
      exact hy (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h0))
    let ψ : K₁ →ₐ[k] S := IsLocalization.liftAlgHom (M := (Ideal.span {(X : k[X])}).primeCompl) (f := aeval t) hunits
    letI : Algebra K₁ S := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower k K₁ S := IsScalarTower.of_algebraMap_eq fun a => (ψ.commutes a).symm
    have hψ : ∀ y : k[X], algebraMap K₁ S (algebraMap k[X] K₁ y) = aeval t y := fun y =>
      IsLocalization.lift_eq (M := (Ideal.span {(X : k[X])}).primeCompl) hunits y
    have hψX : algebraMap K₁ S (algebraMap k[X] K₁ X) = t := by rw [hψ, aeval_X]
    have hI : (maximalIdeal K₁).map (algebraMap K₁ S) = Ideal.span {t} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_span, Set.image_singleton,
        RingHom.comp_apply, hψX]
    haveI : IsLocalHom (algebraMap K₁ S) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap K₁ S)).out 0 2).mpr
      rw [hI, Ideal.span_le, Set.singleton_subset_iff]
      exact ht

    have hinj : Function.Injective (algebraMap K₁ S) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(X : k[X])}).primeCompl z
      have h1 : algebraMap K₁ S (IsLocalization.mk' K₁ a s) * algebraMap K₁ S (algebraMap k[X] K₁ s) =
          aeval t a := by
        rw [← map_mul, IsLocalization.mk'_spec, hψ]
      rw [hz, zero_mul] at h1
      have ha : a = 0 := htr (by rw [map_zero]; exact h1.symm)
      subst ha
      show IsLocalization.mk' K₁ (0 : k[X]) s = 0
      exact IsLocalization.mk'_zero s
    haveI : Module.IsTorsionFree K₁ S := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
    haveI : Module.Flat K₁ S := inferInstance
    haveI : Algebra.EssFiniteType K₁ S := Algebra.EssFiniteType.of_comp k K₁ S

    haveI hlocF : IsLocalRing (S ⧸ Ideal.span {t}) := RegularQuotientEngine.isLocalRing_quotient_span_singleton S ht
    have hregF' : IsRegularLocalRing (S ⧸ Ideal.span {t}) :=
      RegularQuotientEngine.isRegularLocalRing_quotient_span_singleton S ht ht2
    have hnF' : (maximalIdeal (S ⧸ Ideal.span {t})).spanFinrank = n := by
      have := RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_succ_eq S ht ht2
      omega
    haveI hregF : IsRegularLocalRing (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S)) := by rw [hI]; exact hregF'
    have hnF : (maximalIdeal (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S))).spanFinrank = n := by
      rw [spanFinrank_maximalIdeal_quotient_congr hI]; exact hnF'
    haveI hmax : (maximalIdeal K₁).IsMaximal := IsLocalRing.maximalIdeal.isMaximal K₁
    letI : Field (K₁ ⧸ maximalIdeal K₁) := Ideal.Quotient.field (maximalIdeal K₁)
    haveI : (Ideal.span {(X : k[X])}).IsMaximal := by
      exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
    haveI : Algebra.FiniteType k (ResidueField K₁) :=
      Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
    haveI : Module.Finite k (ResidueField K₁) :=
      finite_of_finite_type_of_isJacobsonRing k (ResidueField K₁)
    haveI : PerfectField (K₁ ⧸ maximalIdeal K₁) :=
      Algebra.IsAlgebraic.perfectField (K := k) (L := ResidueField K₁)
    have hF : Algebra.FormallySmooth (K₁ ⧸ maximalIdeal K₁)
        (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S)) :=
      ih (K₁ ⧸ maximalIdeal K₁) (S ⧸ (maximalIdeal K₁).map (algebraMap K₁ S)) hnF
    haveI : Algebra.FormallySmooth (K₁ ⧸ maximalIdeal K₁) ((K₁ ⧸ maximalIdeal K₁) ⊗[K₁] S) :=
      Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal K₁))
    haveI : Algebra.FormallySmooth (ResidueField K₁) ((ResidueField K₁) ⊗[K₁] S) := ‹_›
    haveI : Algebra.FinitePresentation K₁ (Algebra.EssFiniteType.subalgebra K₁ S) :=
      (Algebra.FinitePresentation.of_finiteType (R := K₁) (A := Algebra.EssFiniteType.subalgebra K₁ S)).mp inferInstance
    haveI hS : Algebra.FormallySmooth K₁ S :=
      Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := K₁) (S := S)
        (P := Algebra.EssFiniteType.subalgebra K₁ S) (Algebra.EssFiniteType.submonoid K₁ S)
    haveI : Algebra.FormallySmooth k K₁ := inferInstance
    exact Algebra.FormallySmooth.comp k K₁ S


theorem formallySmooth
    (k : Type u) [Field k] [PerfectField k] (S : Type u) [CommRing S]
    [IsRegularLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] :
    Algebra.FormallySmooth k S :=
  main _ k S rfl

end PhilipponRegularLocalPerfectSmooth

end

section
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
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory

namespace PhilipponRegularSchemeSmooth

set_option backward.isDefEq.respectTransparency false in
theorem mem_smoothLocus
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) [LocallyOfFinitePresentation g]
    (y : Y) (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) :
    y ∈ g.smoothLocus := by
  have hft := LocallyOfFiniteType.stalkMap g y
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(g.stalkMap y).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (g y)
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (g y).asIdeal.primeCompl
    (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let iF : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let iF' : Field ((Spec (.of K)).presheaf.stalk (g y)) := iF
  have : PerfectField ((Spec (.of K)).presheaf.stalk (g y)) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (g y))
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hreg
  exact PhilipponRegularLocalPerfectSmooth.formallySmooth
    ((Spec (.of K)).presheaf.stalk (g y)) (Y.presheaf.stalk y)

theorem smooth
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) :
    Smooth π := by
  have : LocallyOfFinitePresentation π :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType π
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_le_iff.mp
  intro y _
  exact mem_smoothLocus K π y (hreg y)

end PhilipponRegularSchemeSmooth

end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open IsLocalRing Localization

namespace ChildB

private theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.EssFiniteType R S] :
    IsNoetherianRing S := by
  haveI hN : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S hN

end ChildB

theorem etaleRegularAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hreg
  haveI hlo : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)) q

  haveI : Algebra.FormallyUnramified A B := inferInstance
  haveI hIU : Algebra.IsUnramifiedAt A q := by
    unfold Algebra.IsUnramifiedAt
    infer_instance
  haveI hEFTa : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
  haveI hEFT : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := Algebra.EssFiniteType.of_comp A _ _
  haveI hNoeth : IsNoetherianRing (Localization.AtPrime q) :=
    ChildB.isNoetherianRing_of_essFiniteType (Localization.AtPrime (q.comap (algebraMap A B))) _

  have hmap : (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).map
      (algebraMap _ (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal

  have h1 : (maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).spanFinrank := by
    rw [← hmap]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  haveI : Module.Flat A B := inferInstance
  haveI hflat : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := inferInstance

  haveI hlom2 : (maximalIdeal (Localization.AtPrime q)).LiesOver
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))) := by
    constructor
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_iff_not.mpr
      ⟨fun h => IsLocalHom.map_nonunit x h, fun h => h.map (algebraMap _ _)⟩ |>.symm

  have h2 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := Localization.AtPrime (q.comap (algebraMap A B))) (S := Localization.AtPrime q)
    (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B))))
    (maximalIdeal (Localization.AtPrime q))

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h1
    _ = ringKrullDim (Localization.AtPrime (q.comap (algebraMap A B))) :=
        hreg.spanFinrank_maximalIdeal
    _ = ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ((maximalIdeal (Localization.AtPrime q)).height : WithBot ℕ∞) := by
        rw [h2]
        exact_mod_cast le_self_add
    _ = ringKrullDim (Localization.AtPrime q) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end

end S_isRegularLocalRing_localization_atPrime_of_etale_of_comap
end P2MW
export P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap (etaleRegularAt)

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

/-- Standard smooth presentations are étale over a polynomial algebra, whose
prime localizations are regular. -/
theorem regularAt_of_standardSmooth (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.IsStandardSmooth K R] (q : Ideal R) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨n, f, hf, he⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap K R) (RingHom.isStandardSmooth_algebraMap.mpr inferInstance)
  algebraize [f]
  haveI : IsRegularRing K := inferInstance
  haveI : IsRegularRing (MvPolynomial (Fin n) K) :=
    MvPolynomial.isRegularRing_of_isRegularRing K
  exact P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.etaleRegularAt
    (MvPolynomial (Fin n) K) R q
    (IsRegularRing.isRegularLocalRing_localization _)

/-- Smoothness at a prime suffices: choose a standard smooth neighbourhood
and identify its localization with the original local ring. -/
theorem regularAt_of_smoothAt (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.FinitePresentation K R] (p : Ideal R) [hp : p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  letI := hstd
  have hdis : Disjoint (Submonoid.powers f : Set R) (p : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q := p.map (algebraMap R (Localization.Away f))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) p hp hdis
  have heq : q.comap (algebraMap R (Localization.Away f)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) hp hdis
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    regularAt_of_standardSmooth K (Localization.Away f) q
  haveI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    have heq' : (q.comap (algebraMap R (Localization.Away f))).primeCompl = p.primeCompl := by
      ext x
      change x ∉ q.comap (algebraMap R (Localization.Away f)) ↔ x ∉ p
      rw [heq]
    rw [← heq']
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).symm.toRingEquiv)

end PhilipponMultiplicity.AlgebraicGroupCM

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- Smooth schemes over any field have regular local rings. This uses
the previously checked standard-smooth/etale local calculation and
does not assume perfectness of the ground field. -/
theorem PhilipponSmoothSchemeRegular.stalk
    (K : Type u) [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [Smooth π] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let R := Γ(X, U)
  let φ : K →+* R :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom
  letI : Algebra K R := φ.toAlgebra
  have hφ : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv))
    (π.smooth_appLE (isAffineOpen_top _) hU (by simp))
  letI : Algebra.Smooth K R := hφ
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  haveI : p.IsPrime := inferInstance
  letI : IsRegularLocalRing (Localization.AtPrime p) :=
    PhilipponMultiplicity.AlgebraicGroupCM.regularAt_of_smoothAt K R p
  letI : Algebra R (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace PhilipponCompletedStalkRegularity

theorem stalk_regular_iff {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) ↔
      IsRegularLocalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) :=
  PhilipponCompletionRegularity.regular_iff (X.presheaf.stalk x)

/-- A formal local model proves regularity of the actual stalk, without
producing or assuming a Zariski chart. -/
theorem stalk_of_completed_equiv
    {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    (A : Type v) [CommRing A] [IsRegularLocalRing A]
    (e : AdicCompletion (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+* A) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  apply (stalk_regular_iff x).mpr
  exact IsRegularLocalRing.of_ringEquiv e.symm

theorem all_stalks_regular_iff {X : Scheme.{u}} [IsLocallyNoetherian X] :
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) ↔
      ∀ x : X, IsRegularLocalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) := by
  exact forall_congr' (fun x => stalk_regular_iff x)

/-- For a scheme locally of finite type over a perfect field, it is
enough to check regularity on completed stalks at closed points. -/
theorem smooth_of_closed_completions
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hreg : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))) :
    Smooth π := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  haveI : LocallyOfFinitePresentation π :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType π
  have hx (x : X) (hclosed : IsClosed ({x} : Set X)) : x ∈ π.smoothLocus :=
    PhilipponRegularSchemeSmooth.mem_smoothLocus K π x
      ((stalk_regular_iff x).mpr (hreg x hclosed))
  have hempty : ((π.smoothLocus : Set X)ᶜ ∩ closedPoints X) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x h
    exact h.1 (hx x h.2)
  have hcompl := closure_inter_closedPoints π.smoothLocus.isOpen.isClosed_compl
  rw [hempty, closure_empty] at hcompl
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply SetLike.coe_injective
  change (π.smoothLocus : Set X) = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx'
  have hx'' : x ∈ (π.smoothLocus : Set X)ᶜ := hx'
  rw [← hcompl] at hx''
  exact hx''

theorem regular_of_closed_completions
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hreg : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))) :
    ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := by
  letI := smooth_of_closed_completions K π hreg
  exact PhilipponSmoothSchemeRegular.stalk K π

end PhilipponCompletedStalkRegularity

end
end

section
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
end
end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponGenericDimensionFormula

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


end PhilipponGenericDimensionFormula


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section

namespace PhilipponGenericDimensionFormula

lemma isDominant_genericFiberι
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsDominant (f.fiberι (genericPoint Y)) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)) := by
    refine ⟨(f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, PhilipponGenericDominance.genericPoint_eq_of_dominant f⟩, ?_⟩
    exact f.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (f.fiberι (genericPoint Y)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

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

lemma dimension_eq_trdeg_of_genericPoint {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (x : X) (hx : x = genericPoint X) :
    letI := residueAlgebra c x
    topologicalKrullDim X = (Cardinal.toENat (Algebra.trdeg K (X.residueField x)) : WithBot ℕ∞) := by
  letI := residueAlgebra c x
  have h := toENat_trdeg_residueField_eq_topologicalKrullDim_closure c x
  have hcl : closure ({x} : Set X) = Set.univ := by rw [hx]; exact genericPoint_spec X
  have hd : topologicalKrullDim X = topologicalKrullDim (closure ({x} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  exact hd.trans h.symm

/-- Dimensions add along the actual generic fibre, with the structure-field maps retained. -/
theorem dimension_eq_add_genericFiber
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : Y ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    topologicalKrullDim X = topologicalKrullDim Y +
      topologicalKrullDim (f.fiber (genericPoint Y)) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ c)
  let η := genericPoint Y
  let F := Y.residueField η
  let C := f.fiber η
  let s : C ⟶ Spec F := f.fiberToSpecResidueField η
  let t : C ⟶ X := f.fiberι η
  letI : IsIntegral C := AlgebraicGeometry.isIntegral_genericFiber_of_isDominant f
  letI : IsDominant t := isDominant_genericFiberι f
  let u := genericPoint C
  let z := t u
  let E := C.residueField u
  let L := X.residueField z
  letI : Algebra K F := residueAlgebra c η
  letI : Algebra F E := residueAlgebra s u
  letI : Algebra K E := residueAlgebra (t ≫ (f ≫ c)) u
  letI : Algebra K L := residueAlgebra (f ≫ c) z
  letI : Algebra L E := (t.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower t (f ≫ c) u
  have hbase : t ≫ (f ≫ c) = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    change f.fiberι η ≫ (f ≫ c) =
      f.fiberToSpecResidueField η ≫ Spec.map
        ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop ≫
          Y.presheaf.germ ⊤ η trivial ≫ Y.residue η)
    rw [← preimage_residue_comp, Spec.map_preimage, ← Category.assoc, f.fiber_fac]
    exact Category.assoc _ _ _
  letI : IsScalarTower K F E := by
    apply IsScalarTower.of_algebraMap_eq'
    have hmap : (algebraMap F E).comp (algebraMap K F) =
        (residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u).algebraMap := by
      letI : Algebra K E := residueAlgebra
        (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u
      letI : IsScalarTower K F E := residue_base_tower (K := K) (F := F) s u
      exact (IsScalarTower.algebraMap_eq K F E).symm
    exact (hmap.trans (congrArg (fun a => (residueAlgebra a u).algebraMap) hbase.symm)).symm
  letI : IsIso (t.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion t u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (t.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  letI : LocallyOfFiniteType s := MorphismProperty.pullback_snd f
    (Y.fromSpecResidueField η) (inferInstance : LocallyOfFiniteType f)
  have hX := dimension_eq_trdeg_of_genericPoint (f ≫ c) z (PhilipponGenericDominance.genericPoint_eq_of_dominant t)
  have hY := dimension_eq_trdeg_of_genericPoint c η rfl
  have hC := dimension_eq_trdeg_of_genericPoint (K := F) s u rfl
  rw [hX, hY, hC]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K F) : WithBot ℕ∞) +
      (Cardinal.toENat (Algebra.trdeg F E) : WithBot ℕ∞)
  rw [he, ← trdeg_add_eq K F (A := E)]
  simp only [map_add, WithBot.coe_add]

end PhilipponGenericDimensionFormula

end
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationDimensionControl

lemma finite_of_dimension_le_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hd : topologicalKrullDim X ≤ 0) : IsFinite π := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hd
  letI : Subsingleton X := Set.subsingleton_univ_iff.mp
    ((isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology X)).subsingleton_of_isPreirreducible
      PreirreducibleSpace.isPreirreducible_univ)
  exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := π)).mpr inferInstance

lemma dimension_nonneg (X : Scheme.{u}) [IsIntegral X] :
    0 ≤ topologicalKrullDim X := by
  change 0 ≤ Order.krullDim (IrreducibleCloseds X)
  letI : Nonempty (IrreducibleCloseds X) := ⟨{
    carrier := Set.univ
    isIrreducible' := IrreducibleSpace.isIrreducible_univ X
    isClosed' := isClosed_univ }⟩
  exact Order.krullDim_nonneg

lemma eq_one_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : ((r + 1 : ℕ) : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 1 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 1 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [Nat.cast_add, Nat.cast_one,
        WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_one] using h)
    have hd : d = 1 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

lemma eq_zero_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : (r : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 0 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 0 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [add_zero,
        WithBot.coe_add, WithBot.coe_natCast] using h)
    have hd : d = 0 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

/-- The controlled generic curve forces the covering model to preserve
dimension. Its map to the original variety has zero-dimensional generic fibre. -/
theorem dimension_eq_and_genericFiber_dimensions
    (K : Type u) [Field K] {G X N : Scheme.{u}}
    [IsIntegral G] [IsIntegral X] [IsIntegral N]
    (πX : X ⟶ Spec (.of K)) [LocallyOfFiniteType πX]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (a : G ⟶ X) [LocallyOfFiniteType a] [IsDominant a]
    (f : G ⟶ N) [LocallyOfFiniteType f] [IsDominant f]
    (r : ℕ) (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞))
    (hdN : topologicalKrullDim N = (r : WithBot ℕ∞))
    (hdF : topologicalKrullDim (f.fiber (genericPoint N)) ≤ 1) :
    topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim (f.fiber (genericPoint N)) = 1 ∧
      topologicalKrullDim (a.fiber (genericPoint X)) = 0 := by
  have ha := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πX a
  have hf := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πN f
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (a ≫ πX)
  haveI : IsIntegral (a.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant a
  have hza := dimension_nonneg (a.fiber (genericPoint X))
  have hlow : topologicalKrullDim X ≤ topologicalKrullDim G := by
    calc
      topologicalKrullDim X = topologicalKrullDim X + 0 := (add_zero _).symm
      _ ≤ topologicalKrullDim X + topologicalKrullDim (a.fiber (genericPoint X)) :=
        add_le_add (le_refl _) hza
      _ = topologicalKrullDim G := ha.symm
  have hhigh : topologicalKrullDim G ≤ topologicalKrullDim X := by
    calc
      topologicalKrullDim G = (r : WithBot ℕ∞) +
          topologicalKrullDim (f.fiber (genericPoint N)) := hf.trans (by rw [hdN])
      _ ≤ (r : WithBot ℕ∞) + 1 := add_le_add (le_refl _) hdF
      _ = topologicalKrullDim X := by rw [hdX]; simp
  have heq := le_antisymm hhigh hlow
  refine ⟨heq, eq_one_of_nat_add_eq r _ ?_, eq_zero_of_nat_add_eq (r + 1) _ ?_⟩
  · simpa only [heq, hdX, hdN] using hf
  · simpa only [heq, hdX] using ha

end PhilipponAlterationDimensionControl

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponProperGenericFiniteness

/-- The finite open in the alteration definition gives a finite generic
fiber. The argument retains the actual restriction map and point. -/
theorem finite_genericFiber_of_finite_open
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsProper p]
    (U : X.Opens) [Nonempty U] [IsFinite (p ∣_ U)] :
    IsFinite (p.fiberToSpecResidueField (genericPoint X)) := by
  let η := genericPoint X
  have hηU : η ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hfin := (p ∣_ U).finite_preimage_singleton ηU
  have hpre : (p ⁻¹' {η}).Finite := by
    apply (hfin.image (p ⁻¹ᵁ U).ι).subset
    intro y hy
    change p y = η at hy
    let yU : (p ⁻¹ᵁ U).toScheme := ⟨y, by change p y ∈ U; rw [hy]; exact hηU⟩
    refine ⟨yU, ?_, rfl⟩
    change (p ∣_ U) yU = ηU
    apply Subtype.ext
    exact (morphismRestrict_base_coe p U yU).trans hy
  haveI : Finite (p.fiber η) := (p.fiberHomeo η).finite_iff.mpr hpre
  haveI : IsProper (p.fiberToSpecResidueField η) :=
    MorphismProperty.pullback_snd p (X.fromSpecResidueField η) inferInstance
  haveI : LocallyQuasiFinite (p.fiberToSpecResidueField η) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (p.fiberToSpecResidueField η)
      (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- A proper morphism with finite generic fiber is finite on a nonempty
open of its integral target, in the exact form required by alterations. -/
theorem exists_finite_open_of_finite_genericFiber
    {Y X : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) [IsProper p]
    [IsFinite (p.fiberToSpecResidueField (genericPoint X))] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite (p ∣_ W) := by
  let η := genericPoint X
  have hF : (Set.univ : Set (p.fiber η)).Finite := by
    simpa only [Set.preimage_univ] using
      (p.fiberToSpecResidueField η).finite_preimage
        (Set.finite_univ : (Set.univ : Set (Spec (X.residueField η))).Finite)
  have hpη : (p ⁻¹' {η}).Finite := by
    rw [← p.range_fiberι η]
    simpa only [Set.image_univ] using hF.image (p.fiberι η)
  obtain ⟨W, hηW, hfinite⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton p η hpη
  exact ⟨W, ⟨⟨η, hηW⟩⟩, hfinite⟩

/-- A proper dominant finite-type map between integral varieties whose
source has no larger dimension is finite over a nonempty target open.
The target dimension is explicitly finite; equality of infinite
dimensions is not used to cancel a generic-fiber dimension. -/
theorem exists_finite_open_of_dimension_le
    (K : Type u) [Field K] {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (p : Y ⟶ X) [IsProper p] [IsDominant p]
    (d : ℕ) (hdX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hle : topologicalKrullDim Y ≤ topologicalKrullDim X) :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite (p ∣_ W) := by
  have hdim := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K π p
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ π)
  letI : IsIntegral (p.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant p
  have hnonneg := PhilipponAlterationDimensionControl.dimension_nonneg
    (p.fiber (genericPoint X))
  have hge : topologicalKrullDim X ≤ topologicalKrullDim Y := by
    rw [hdim]
    simpa only [add_zero] using add_le_add (le_refl (topologicalKrullDim X)) hnonneg
  have heq : topologicalKrullDim Y = topologicalKrullDim X := le_antisymm hle hge
  have hzero : topologicalKrullDim (p.fiber (genericPoint X)) = 0 :=
    PhilipponAlterationDimensionControl.eq_zero_of_nat_add_eq d _ (by
      simpa only [heq, hdX] using hdim)
  haveI : LocallyOfFiniteType (p.fiberToSpecResidueField (genericPoint X)) :=
    MorphismProperty.pullback_snd p (X.fromSpecResidueField (genericPoint X)) inferInstance
  haveI : IsFinite (p.fiberToSpecResidueField (genericPoint X)) :=
    PhilipponAlterationDimensionControl.finite_of_dimension_le_zero
      (X.residueField (genericPoint X)) _ hzero.le
  exact exists_finite_open_of_finite_genericFiber p

/-- A proper generically finite map of integral varieties cannot
increase dimension. This supplies the dimension bound required by
algebraic-field descent of the regular projective alteration. -/
theorem dimension_le_of_finite_open
    (K : Type u) [Field K] {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (p : Y ⟶ X) [IsProper p] [IsDominant p]
    (U : X.Opens) [Nonempty U] [IsFinite (p ∣_ U)] :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  haveI : IsFinite (p.fiberToSpecResidueField (genericPoint X)) :=
    finite_genericFiber_of_finite_open p U
  haveI : IsLocallyArtinian (p.fiber (genericPoint X)) :=
    IsLocallyArtinian.of_locallyQuasiFinite (p.fiberToSpecResidueField (genericPoint X))
  have hzero := topologicalKrullDim_zero_of_discreteTopology (p.fiber (genericPoint X))
  calc
    topologicalKrullDim Y = topologicalKrullDim X +
        topologicalKrullDim (p.fiber (genericPoint X)) :=
      PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K π p
    _ ≤ topologicalKrullDim X + 0 := add_le_add (le_refl _) hzero
    _ = topologicalKrullDim X := add_zero _

end PhilipponProperGenericFiniteness

end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

noncomputable abbrev functionFieldAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra

noncomputable abbrev chartAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom.toAlgebra

lemma chart_functionField_tower {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    letI := functionFieldAlgebra π
    letI := chartAlgebra π U
    IsScalarTower K Γ(X, U) X.functionField := by
  letI := functionFieldAlgebra π
  letI := chartAlgebra π U
  apply IsScalarTower.of_algebraMap_eq'
  symm
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp) ≫
    X.germToFunctionField U).hom =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom
  have h : π.appLE ⊤ U (by simp) ≫ X.germToFunctionField U =
      π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
      X.presheaf.germ_res]
    rfl
  exact congrArg CommRingCat.Hom.hom
    (congrArg (fun q => (Scheme.ΓSpecIso (.of K)).inv ≫ q) h)

lemma chart_finiteType {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := chartAlgebra π U
    Algebra.FiniteType K Γ(X, U) := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)

lemma functionField_essFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    Algebra.EssFiniteType K X.functionField := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  letI := chartAlgebra π U
  letI := chart_functionField_tower π U
  letI := chart_finiteType π U hU
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp K Γ(X, U) X.functionField

/-- A finite separating transcendence basis of the actual function field. -/
theorem exists_separating_function_field_parameters
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
  letI := functionFieldAlgebra π
  letI := functionField_essFiniteType π
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K X.functionField
  have hr : Set.range ((↑) : s → X.functionField) = (s : Set X.functionField) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
    have h := hs.isAlgebraic_field
    rw [hr] at h
    exact h
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField :=
    Algebra.EssFiniteType.of_comp K _ _
  exact ⟨s, hs, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩

end PhilipponAlterationProjection

end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponAlterationProjection

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


lemma dimension_eq_of_open_immersion {K : Type u} [Field K]
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (f : U ⟶ W) [IsOpenImmersion f]
    (d : W ⟶ Spec (.of K)) [LocallyOfFiniteType d] :
    topologicalKrullDim U = topologicalKrullDim W := by
  let u := genericPoint U
  let L := W.residueField (f u)
  let E := U.residueField u
  letI : Algebra K L := residueAlgebra d (f u)
  letI : Algebra K E := residueAlgebra (f ≫ d) u
  letI : Algebra L E := (f.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower f d u
  letI : IsIso (f.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion f u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  have hW := toENat_trdeg_residueField_eq_topologicalKrullDim_closure d (f u)
  have hU := toENat_trdeg_residueField_eq_topologicalKrullDim_closure (f ≫ d) u
  have hgen : f u = genericPoint W := genericPoint_eq_of_isOpenImmersion f
  have hclW : closure ({f u} : Set W) = Set.univ := by rw [hgen]; exact genericPoint_spec W
  have hclU : closure ({u} : Set U) = Set.univ := genericPoint_spec U
  have hdW : topologicalKrullDim W = topologicalKrullDim (closure ({f u} : Set W)) := by
    rw [hclW]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ W)
      (Homeomorph.Set.univ W).isHomeomorph).symm
  have hdU : topologicalKrullDim U = topologicalKrullDim (closure ({u} : Set U)) := by
    rw [hclU]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ U)
      (Homeomorph.Set.univ U).isHomeomorph).symm
  rw [hdU, hdW, ← hU, ← hW]
  change (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞)
  rw [he]

lemma dimension_eq_card_of_function_field_basis {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] (S : Finset X.functionField)
    (hS : letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
      IsTranscendenceBasis K ((↑) : S → X.functionField)) :
    topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) := by
  letI : Algebra K X.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let L := X.residueField (genericPoint X)
  letI : Algebra K L := residueAlgebra π (genericPoint X)
  letI : Algebra X.functionField L := (X.residue (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower K X.functionField L := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  have hbij : Function.Bijective (X.residue (genericPoint X)) :=
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩
  let e : X.functionField ≃ₐ[K] L :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom K X.functionField L) hbij
  have he : Algebra.trdeg K X.functionField = Algebra.trdeg K L := e.trdeg_eq
  have hd := toENat_trdeg_residueField_eq_topologicalKrullDim_closure π (genericPoint X)
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hdim : topologicalKrullDim X = topologicalKrullDim (closure ({genericPoint X} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  rw [hdim, ← hd]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) = _
  rw [← he, ← hS.cardinalMk_eq_trdeg]
  simp

end PhilipponAlterationProjection

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponFieldModelDimension
open PhilipponAlterationProjection

lemma affine_dimension_eq_fraction_trdeg
    (k A F : Type u) [Field k] [CommRing A] [IsDomain A] [Field F]
    [Algebra k A] [Algebra A F] [Algebra k F] [IsScalarTower k A F]
    [Algebra.FiniteType k A] [IsFractionRing A F] :
    topologicalKrullDim (Spec (.of A)) =
      (Cardinal.toENat (Algebra.trdeg k F) : WithBot ℕ∞) := by
  haveI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr (IsFractionRing.injective A F)
  letI : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have h := trdeg_add_eq k A (A := F)
  rw [trdeg_eq_zero (R := A) (A := F), add_zero] at h
  change topologicalKrullDim (PrimeSpectrum A) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A, h]

lemma dimension_eq_functionField_trdeg
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    topologicalKrullDim S =
      (Cardinal.toENat (Algebra.trdeg k S.functionField) : WithBot ℕ∞) := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint S ∈ (⊤ : S.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint S, hη⟩⟩
  letI := chartAlgebra π U
  letI := chart_finiteType π U hU
  letI := chart_functionField_tower π U
  letI := functionField_isFractionRing_of_isAffineOpen S U hU
  have hdim := PhilipponAlterationProjection.dimension_eq_of_open_immersion hU.fromSpec π
  exact hdim.symm.trans (affine_dimension_eq_fraction_trdeg k Γ(S, U) S.functionField)

end PhilipponFieldModelDimension

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- An integral scheme locally of finite type over any field has a
finite natural-number dimension. No perfectness assumption is needed. -/
theorem PhilipponFiniteTypeDimension.exists_nat
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    ∃ d : ℕ, topologicalKrullDim X = (d : WithBot ℕ∞) := by
  letI := PhilipponAlterationProjection.functionFieldAlgebra π
  letI := PhilipponAlterationProjection.functionField_essFiniteType π
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 k X.functionField)
  refine ⟨d, (PhilipponFieldModelDimension.dimension_eq_functionField_trdeg k π).trans ?_⟩
  rw [hd]
  simp

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponFormalProjectiveAlterationCriterion

/-- Checking explicit formal power-series models only at closed points
proves regularity of every stalk. No algebraization of the models is used. -/
theorem regular_of_closed_models
    (K : Type u) [Field K] [PerfectField K] {Y : Scheme.{u}}
    (σ : Y ⟶ Spec (.of K)) [LocallyOfFiniteType σ]
    (hmodels : ∀ y : Y, IsClosed ({y} : Set Y) →
      ∃ r : ℕ, Nonempty (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y) ≃+* MvPowerSeries (Fin r) K)) :
    ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
  apply PhilipponCompletedStalkRegularity.regular_of_closed_completions K σ
  intro y hy
  obtain ⟨r, ⟨e⟩⟩ := hmodels y hy
  letI := PhilipponPowerSeriesRegularity.fin K r
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- A dominant projective cover of no larger dimension with the displayed
closed-point formal models satisfies all the alteration conclusions for
the same source, map and projective embedding. -/
theorem exists_of_formal_cover
    (K : Type u) [Field K] [PerfectField K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Spec (.of K)) [IsSeparated π] [LocallyOfFiniteType π]
    (a : Y ⟶ X) [IsDominant a]
    (hle : topologicalKrullDim Y ≤ topologicalKrullDim X)
    (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π K m = a ≫ π)
    (hmodels : ∀ y : Y, IsClosed ({y} : Set Y) →
      ∃ r : ℕ, Nonempty (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y) ≃+* MvPowerSeries (Fin r) K)) :
    IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) := by
  haveI : IsProper (a ≫ π) := by rw [← hj]; infer_instance
  haveI : IsProper a := IsProper.of_comp (f := a) (g := π)
  haveI : Surjective a := by
    refine ⟨Set.range_eq_univ.mp ?_⟩
    exact a.isClosedMap.isClosed_range.closure_eq.symm.trans a.denseRange.closure_range
  have hreg := regular_of_closed_models K (a ≫ π) hmodels
  obtain ⟨d, hd⟩ := PhilipponFiniteTypeDimension.exists_nat K π
  exact ⟨inferInstance, inferInstance, hreg,
    PhilipponProperGenericFiniteness.exists_finite_open_of_dimension_le K π a d hd hle⟩

end PhilipponFormalProjectiveAlterationCriterion

end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  obtain ⟨Y, a, hY, hdom, hle, hmodels, m, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_dominant_projective_formal_powerSeries_cover
      K π n ι hι hnormal hdim
  letI : IsIntegral Y := hY
  letI : IsDominant a := hdom
  letI : IsClosedImmersion j := hj
  haveI : IsProper π := by rw [← hι]; infer_instance
  obtain ⟨hproper, hsurj, hreg, hfinite⟩ :=
    PhilipponFormalProjectiveAlterationCriterion.exists_of_formal_cover
      K π a hle m j hjbase hmodels
  exact ⟨Y, a, hY, hproper, hsurj, hreg, hfinite, m, j, hj, hjbase⟩

end
end

#print axioms PhilipponPowerSeriesRegularity.powerSeries
#print axioms PhilipponPowerSeriesRegularity.fin
#print axioms PhilipponPowerSeriesRegularity.mvPowerSeries
#print axioms PhilipponMultiplicity.NoetherianCompletion.exists_powerSeriesMap
#print axioms PhilipponMultiplicity.NoetherianCompletion.powerSeriesMap_surjective
#print axioms PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
#print axioms PhilipponCompletionRegularity.dimension_eq_of_flat_local_map
#print axioms PhilipponCompletionRegularity.dimension_eq
#print axioms PhilipponCompletionRegularity.regular_iff
#print axioms PhilipponRegularLocalPerfectSmooth.formallySmooth
#print axioms PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType
#print axioms PhilipponRegularSchemeSmooth.smooth
#print axioms P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.etaleRegularAt
#print axioms PhilipponMultiplicity.AlgebraicGroupCM.regularAt_of_standardSmooth
#print axioms PhilipponMultiplicity.AlgebraicGroupCM.regularAt_of_smoothAt
#print axioms PhilipponSmoothSchemeRegular.stalk
#print axioms PhilipponCompletedStalkRegularity.stalk_regular_iff
#print axioms PhilipponCompletedStalkRegularity.stalk_of_completed_equiv
#print axioms PhilipponCompletedStalkRegularity.all_stalks_regular_iff
#print axioms PhilipponCompletedStalkRegularity.smooth_of_closed_completions
#print axioms PhilipponCompletedStalkRegularity.regular_of_closed_completions
#print axioms PhilipponGenericDominance.genericFiber_inclusion
#print axioms PhilipponGenericDominance.of_recovered_generic_cover
#print axioms PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber
#print axioms PhilipponAlterationDimensionControl.finite_of_dimension_le_zero
#print axioms PhilipponAlterationDimensionControl.dimension_nonneg
#print axioms PhilipponAlterationDimensionControl.eq_one_of_nat_add_eq
#print axioms PhilipponAlterationDimensionControl.eq_zero_of_nat_add_eq
#print axioms PhilipponAlterationDimensionControl.dimension_eq_and_genericFiber_dimensions
#print axioms PhilipponProperGenericFiniteness.finite_genericFiber_of_finite_open
#print axioms PhilipponProperGenericFiniteness.exists_finite_open_of_finite_genericFiber
#print axioms PhilipponProperGenericFiniteness.exists_finite_open_of_dimension_le
#print axioms PhilipponProperGenericFiniteness.dimension_le_of_finite_open
#print axioms PhilipponAlterationProjection.functionField_essFiniteType
#print axioms PhilipponAlterationProjection.exists_separating_function_field_parameters
#print axioms PhilipponAlterationProjection.residue_tower
#print axioms PhilipponFieldModelDimension.affine_dimension_eq_fraction_trdeg
#print axioms PhilipponFieldModelDimension.dimension_eq_functionField_trdeg
#print axioms PhilipponFiniteTypeDimension.exists_nat
#print axioms PhilipponFormalProjectiveAlterationCriterion.regular_of_closed_models
#print axioms PhilipponFormalProjectiveAlterationCriterion.exists_of_formal_cover
#print axioms solution
