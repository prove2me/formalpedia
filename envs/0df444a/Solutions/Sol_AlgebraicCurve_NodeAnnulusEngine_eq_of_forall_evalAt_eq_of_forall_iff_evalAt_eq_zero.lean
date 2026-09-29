-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/134fa27c-bb56-53de-bb81-ef153bcc2e3b

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_IsLocalRing_isReduced_quotient_map_of_flat_of_locallyPrincipalOverring
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_of_linearDisjoint_of_transcendental
import Theorems.Thm_IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open scoped IntermediateField

namespace R1AF8D2b

section Centre

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

def cen (N : Subring F) (P : Place L F) : Ideal N :=
  Ideal.span {g : N | (g : F) ∈ P.toValuationSubring.nonunits}

variable (N : Subring F) (P : Place L F)

def toPlaceHom (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring) : N →+* P.toValuationSubring :=
  (N.subtype).codRestrict P.toValuationSubring (fun g => h g g.2)

theorem cen_eq_comap (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring) :
    cen N P = (maximalIdeal P.toValuationSubring).comap (toPlaceHom N P h) := by
  have hset : {g : N | (g : F) ∈ P.toValuationSubring.nonunits} =
      ((maximalIdeal P.toValuationSubring).comap (toPlaceHom N P h) : Set N) := by
    ext g
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_comap]
    rw [show (g : F) = ((toPlaceHom N P h g : P.toValuationSubring) : F) from rfl,
      ValuationSubring.coe_mem_nonunits_iff]
  unfold cen
  rw [hset, Ideal.span_eq]

theorem mem_cen_iff (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring) (g : N) :
    g ∈ cen N P ↔ (toPlaceHom N P h g) ∈ maximalIdeal P.toValuationSubring := by
  rw [cen_eq_comap N P h, Ideal.mem_comap]

theorem mem_maximalIdeal_iff_ord_ne_zero {f : F} (hf0 : f ≠ 0) (hf : f ∈ P.toValuationSubring) :
    (⟨f, hf⟩ : P.toValuationSubring) ∈ maximalIdeal P.toValuationSubring ↔ P.ord f ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : P.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hϖ
  have hcoe : f = ((u : P.toValuationSubring) : F) * ((ϖ : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  have hord : P.ord f = n := by rw [hcoe, P.ord_unit_smul_zpow u hϖ (n : ℤ)]
  rw [hu, hord]
  constructor
  · intro hmem hn
    have hn0 : n = 0 := by exact_mod_cast hn
    rw [hn0, pow_zero, mul_one] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem u.isUnit
  · intro hn
    have hn0 : n ≠ 0 := by exact_mod_cast hn
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hϖunit : IsUnit ϖ := by
      have := isUnit_of_mul_isUnit_right hunit
      exact (isUnit_pow_iff hn0).mp this
    exact hϖ.not_isUnit hϖunit

theorem mem_cen_iff_ord_ne_zero (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring) (g : N)
    (hg0 : (g : F) ≠ 0) : g ∈ cen N P ↔ P.ord (g : F) ≠ 0 := by
  rw [mem_cen_iff N P h, ← mem_maximalIdeal_iff_ord_ne_zero P hg0 (h g g.2)]
  rfl

theorem algebraMap_not_mem_cen (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring)
    {c : L} (hc : c ≠ 0) (hcN : algebraMap L F c ∈ N) :
    (⟨algebraMap L F c, hcN⟩ : N) ∉ cen N P := by
  rw [mem_cen_iff N P h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine IsUnit.of_mul_eq_one (b := ⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩) (Subtype.ext ?_)
  change algebraMap L F c * algebraMap L F c⁻¹ = 1
  rw [← map_mul, mul_inv_cancel₀ hc, map_one]

end Centre

section Lengths

variable {A : Type*} [CommRing A]

theorem subsingleton_localizedModule_quotient {𝔓 : Ideal A} [𝔓.IsPrime] {I : Ideal A} {x : A}
    (hxI : x ∈ I) (hx : x ∉ 𝔓) :
    Subsingleton (LocalizedModule 𝔓.primeCompl (A ⧸ I)) := by
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨x, hx⟩, ?_⟩
      have hm : (x : A) • m = 0 := by
        obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
        rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
        exact I.mul_mem_right _ hxI
      have hm' : (x : A) • m' = 0 := by
        obtain ⟨m', rfl⟩ := Ideal.Quotient.mk_surjective m'
        rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
        exact I.mul_mem_right _ hxI
      change (⟨x, hx⟩ : 𝔓.primeCompl) • s' • m = (⟨x, hx⟩ : 𝔓.primeCompl) • s • m'
      rw [Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def, smul_comm, hm, smul_zero,
        smul_comm, hm', smul_zero]

theorem length_localizedModule_quotient_span_eq_zero {𝔓 : Ideal A} [𝔓.IsPrime] {x : A} (hx : x ∉ 𝔓) :
    Module.length (Localization.AtPrime 𝔓) (LocalizedModule 𝔓.primeCompl (A ⧸ Ideal.span {x})) = 0 := by
  haveI := subsingleton_localizedModule_quotient (Ideal.subset_span (Set.mem_singleton x)) hx
  exact Module.length_eq_zero

end Lengths

section Assembly

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
variable {R : Type*} [CommRing R]

def OrdEqLength (S : Set (Place L F)) (N : Subring F) (f : N) : Prop :=
  ∀ P ∈ S, ∀ (𝔭 : Ideal N) [𝔭.IsPrime], cen N P = 𝔭 → f ∈ 𝔭 →
    (((P.ord (f : F)).toNat : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl (N ⧸ Ideal.span {f}))

def LengthMul (N : Subring F) (j : N →+* R) (ϖN : N) (f : N) : Prop :=
  ∀ (𝔭 : Ideal N) [𝔭.IsPrime], ϖN ∉ 𝔭 → f ∈ 𝔭 → ∀ Q : PrimeSpectrum R, Q.asIdeal.comap j = 𝔭 →
    Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (R ⧸ Ideal.span {j f})) =
      Module.length (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl (N ⧸ Ideal.span {f})) *
        Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl (R ⧸ 𝔭.map j))

end Assembly

section ResidualC

open TensorProduct

variable {A : Type*} [CommRing A]

def locQuotEquiv (S : Submonoid A) (I : Ideal A) :
    LocalizedModule S (A ⧸ I) ≃ₗ[Localization S] Localization S ⧸ I.map (algebraMap A (Localization S)) :=
  (IsLocalizedModule.isBaseChange S (Localization S)
      (LocalizedModule.mkLinearMap S (A ⧸ I))).equiv.symm ≪≫ₗ
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization S) I).toLinearEquiv.symm

theorem length_localizedModule_quotient (S : Submonoid A) (I : Ideal A) :
    Module.length (Localization S) (LocalizedModule S (A ⧸ I)) =
      Module.length (Localization S) (Localization S ⧸ I.map (algebraMap A (Localization S))) :=
  (locQuotEquiv S I).length_eq

theorem length_quotient_span_algebraMap_eq_mul {B : Type*} [CommRing B] [Algebra A B] [Module.Flat A B]
    (𝔭 : Ideal A) [𝔭.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver 𝔭] (a : A) :
    Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (B ⧸ Ideal.span {algebraMap A B a})) =
      Module.length (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl (A ⧸ Ideal.span {a})) *
        Module.length (Localization.AtPrime Q)
          (LocalizedModule Q.primeCompl (B ⧸ 𝔭.map (algebraMap A B))) := by
  letI : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime Q) := Localization.AtPrime.algebraOfLiesOver 𝔭 Q
  set A' := Localization.AtPrime 𝔭 with hA'
  set B' := Localization.AtPrime Q with hB'
  haveI : IsLocalHom (algebraMap A' B') :=
    Localization.isLocalHom_localRingHom 𝔭 Q (algebraMap A B) Ideal.LiesOver.over

  have key := IsLocalRing.length_baseChange A' B' (A' ⧸ Ideal.span {algebraMap A A' a})

  have hmapA : (Ideal.span {a}).map (algebraMap A A') = Ideal.span {algebraMap A A' a} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmapB : (Ideal.span {algebraMap A B a}).map (algebraMap B B') = Ideal.span {algebraMap A B' a} := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  have hmapAB : (Ideal.span {algebraMap A A' a}).map (algebraMap A' B') = Ideal.span {algebraMap A B' a} := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  have hmax : (maximalIdeal A').map (algebraMap A' B') = (𝔭.map (algebraMap A B)).map (algebraMap B B') := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

  have h1 : Module.length B' (LocalizedModule Q.primeCompl (B ⧸ Ideal.span {algebraMap A B a})) =
      Module.length B' (B' ⊗[A'] (A' ⧸ Ideal.span {algebraMap A A' a})) := by
    rw [length_localizedModule_quotient, hmapB, ← hmapAB]
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' (Ideal.span {algebraMap A A' a})).toLinearEquiv.length_eq
  have h2 : Module.length A' (LocalizedModule 𝔭.primeCompl (A ⧸ Ideal.span {a})) =
      Module.length A' (A' ⧸ Ideal.span {algebraMap A A' a}) := by
    rw [length_localizedModule_quotient, hmapA]
  have h3 : Module.length B' (LocalizedModule Q.primeCompl (B ⧸ 𝔭.map (algebraMap A B))) =
      Module.length B' (B' ⧸ (maximalIdeal A').map (algebraMap A' B')) := by
    rw [length_localizedModule_quotient, hmax]
  rw [h1, h2, h3, key]

theorem lengthMul_of_flat {F : Type*} [Field F] {R : Type*} [CommRing R]
    (N : Subring F) (j : N →+* R) (hflat : j.Flat) (ϖN f : N) : LengthMul N j ϖN f := by
  intro 𝔭 _ _ _ Q hQ
  letI : Algebra N R := j.toAlgebra
  haveI : Module.Flat N R := hflat
  haveI : Q.asIdeal.LiesOver 𝔭 := ⟨hQ.symm⟩
  exact length_quotient_span_algebraMap_eq_mul 𝔭 Q.asIdeal f

end ResidualC

section Crossing

variable {W : Type*} [CommRing W]

def evalZero (t : W) : UVCrossingModel W t →+* W ⧸ Ideal.span {t} :=
  Ideal.Quotient.lift (uvCrossingIdeal W t)
    ((Ideal.Quotient.mk (Ideal.span {t})).comp (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)))
    (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      suffices h : ((Ideal.Quotient.mk (Ideal.span {t})).comp (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)))
          ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C t) = 0 by
        rw [h, mul_zero]
      rw [RingHom.comp_apply, map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C,
        zero_mul, zero_sub, map_neg, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton t))

theorem evalZero_const (t w : W) : evalZero t (const t w) = Ideal.Quotient.mk (Ideal.span {t}) w := by
  show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = _
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_C]

theorem not_isUnit_const_pow (π : W) (hπ : ¬ IsUnit π) (E : ℕ) (hE : 1 ≤ E) :
    ¬ IsUnit (const (π ^ E) π) := by
  intro h
  have h' := h.map (evalZero (π ^ E))
  rw [evalZero_const] at h'
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {π ^ E}) (↑(h'.unit⁻¹) : W ⧸ Ideal.span {π ^ E})
  have hmul : Ideal.Quotient.mk (Ideal.span {π ^ E}) (π * u) = 1 := by
    rw [map_mul, hu, IsUnit.mul_val_inv]
  rw [← (Ideal.Quotient.mk (Ideal.span {π ^ E})).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hmul
  obtain ⟨c, hc⟩ := hmul
  obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE
  apply hπ
  refine IsUnit.of_mul_eq_one (b := u - π ^ E' * c) ?_
  have : π * u - 1 = π ^ (1 + E') * c := hc
  linear_combination this

end Crossing

section Instance

variable {F : Type*} [Field F]

theorem flat_comp_completion (N : Subring F) [IsNoetherianRing N] [IsLocalRing N] {R : Type*} [CommRing R]
    (ι : AdicCompletion (maximalIdeal N) N ≃+* R) :
    (ι.toRingHom.comp (algebraMap N (AdicCompletion (maximalIdeal N) N))).Flat :=
  RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) (RingHom.Flat.of_bijective ι.bijective)

theorem mem_maximalIdeal_of_not_isUnit_map (N : Subring F) [IsLocalRing N] {R : Type*} [CommRing R]
    (j : N →+* R) (x : N) (hx : ¬ IsUnit (j x)) : x ∈ maximalIdeal N :=
  (IsLocalRing.mem_maximalIdeal x).mpr fun h => hx (h.map j)

end Instance

section CentreDVR

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem length_quotient_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (I : Ideal A) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ I.map e) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : Module A (B ⧸ I.map e) := Module.compHom _ e.toRingHom
  haveI : IsScalarTower A B (B ⧸ I.map e) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj : Function.Surjective (algebraMap A B) := e.surjective
  rw [← Module.length_eq_of_surjective (S := A) (R := B) (M := B ⧸ I.map e) hsurj]

  have hle : I ≤ (I.map e).comap e.toRingHom := fun x hx => Ideal.mem_comap.mpr (Ideal.mem_map_of_mem e hx)
  have hge : (I.map e).comap e.toRingHom ≤ I := by
    intro x hx
    have h := (Ideal.comap_map_of_bijective e e.bijective).le (Ideal.mem_comap.mpr (Ideal.mem_comap.mp hx))
    exact h
  let φ : A ⧸ I →+* B ⧸ I.map e := Ideal.quotientMap (I.map e) e.toRingHom hle
  have hφbij : Function.Bijective φ := by
    constructor
    · exact Ideal.quotientMap_injective' hge
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨Ideal.Quotient.mk I x, rfl⟩
  let ψ : (A ⧸ I) →ₗ[A] (B ⧸ I.map e) :=
    { toFun := φ
      map_add' := fun x y => map_add φ x y
      map_smul' := by
        intro a x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk (I.map e) (e.toRingHom (a * x)) =
          Ideal.Quotient.mk (I.map e) (e.toRingHom a * e.toRingHom x)
        rw [map_mul] }
  exact (LinearEquiv.ofBijective ψ hφbij).length_eq

theorem length_quotient_span_eq_ord {K : Type*} [Field K] [Algebra K F] (P : Place K F)
    (x : P.toValuationSubring) (hx : x ≠ 0) :
    Module.length P.toValuationSubring (P.toValuationSubring ⧸ Ideal.span {x}) = ((P.ord (x : F)).toNat : ℕ∞) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have hord : P.ord (x : F) = n := by
    have hcoe : (x : F) = ((u : P.toValuationSubring) : F) * ((ϖ : F) ^ (n : ℤ)) := by
      rw [hu]; push_cast; rw [zpow_natCast]
    rw [hcoe, P.ord_unit_smul_zpow u hϖ (n : ℤ)]
  have hspan : Ideal.span {x} = maximalIdeal P.toValuationSubring ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton, hu]
    exact (Associated.refl _).mul_left _ |>.trans ((associated_unit_mul_left _ _ u.isUnit))
  rw [hord, hspan, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  simp

variable (N : Subring F) (P : Place L F) {F₀ : Subfield F} (O₀ : ValuationSubring F₀)
  (hO₀ : ∀ x : F₀, x ∈ O₀ ↔ (x : F) ∈ P.toValuationSubring)
  (hN : (N : Set F) ⊆ F₀) (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring)

def toRestricted : N →+* O₀ where
  toFun g := ⟨⟨g, hN g.2⟩, (hO₀ _).mpr (h g g.2)⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

theorem toRestricted_injective : Function.Injective (toRestricted N P O₀ hO₀ hN h) := by
  intro a b hab
  have := congrArg (fun z : O₀ => ((z : F₀) : F)) hab
  exact Subtype.ext this

theorem isUnit_toRestricted [(cen N P).IsPrime] (s : (cen N P).primeCompl) :
    IsUnit (toRestricted N P O₀ hO₀ hN h s) := by
  have hs : (s : N) ∉ cen N P := s.2
  rw [mem_cen_iff N P h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hs

  have hs0 : ((s : N) : F) ≠ 0 := by
    intro h0
    apply hs.ne_zero
    exact Subtype.ext h0
  obtain ⟨t, ht⟩ := hs
  have htinv : ((t⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring).1 = ((s : N) : F)⁻¹ := by
    have h1 : ((t : P.toValuationSubring) : F) * ((t⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring) = 1 := by
      have h0 := congrArg (fun z : P.toValuationSubring => (z : F)) (Units.mul_inv t)
      rw [MulMemClass.coe_mul] at h0
      exact h0
    have ht' : ((t : P.toValuationSubring) : F) = ((s : N) : F) := by rw [ht]; rfl
    rw [ht'] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hmem : (⟨((s : N) : F)⁻¹, inv_mem (hN (s : N).2)⟩ : F₀) ∈ O₀ := by
    rw [hO₀]
    show ((s : N) : F)⁻¹ ∈ P.toValuationSubring
    rw [← htinv]
    exact SetLike.coe_mem _
  refine ⟨⟨toRestricted N P O₀ hO₀ hN h s, ⟨⟨((s : N) : F)⁻¹, inv_mem (hN (s : N).2)⟩, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext; apply Subtype.ext
    show ((s : N) : F) * ((s : N) : F)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  · apply Subtype.ext; apply Subtype.ext
    show ((s : N) : F)⁻¹ * ((s : N) : F) = 1
    exact inv_mul_cancel₀ hs0

def locToRestricted [(cen N P).IsPrime] : Localization.AtPrime (cen N P) →+* O₀ :=
  IsLocalization.lift (M := (cen N P).primeCompl) (isUnit_toRestricted N P O₀ hO₀ hN h)

theorem locToRestricted_algebraMap [(cen N P).IsPrime] (g : N) :
    locToRestricted N P O₀ hO₀ hN h (algebraMap N _ g) = toRestricted N P O₀ hO₀ hN h g := by
  unfold locToRestricted
  exact IsLocalization.lift_eq _ _

theorem locToRestricted_injective [(cen N P).IsPrime] : Function.Injective (locToRestricted N P O₀ hO₀ hN h) := by
  unfold locToRestricted
  rw [IsLocalization.lift_injective_iff]
  intro a b
  have hinj : Function.Injective (algebraMap N (Localization.AtPrime (cen N P))) :=
    IsLocalization.injective (Localization.AtPrime (cen N P)) (cen N P).primeCompl_le_nonZeroDivisors
  constructor
  · intro hab
    rw [hinj hab]
  · intro hab
    rw [toRestricted_injective N P O₀ hO₀ hN h hab]

theorem locToRestricted_surjective [(cen N P).IsPrime]
    (hfrac : ∀ x : F, x ∈ F₀ → ∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀)
    (hsurj : ∀ x : F, x ∈ P.toValuationSubring → (∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀) →
      ∃ r s : N, s ∉ cen N P ∧ x * s = r) :
    Function.Surjective (locToRestricted N P O₀ hO₀ hN h) := by
  unfold locToRestricted
  rw [IsLocalization.lift_surjective_iff]
  intro v
  have hvP : ((v : F₀) : F) ∈ P.toValuationSubring := (hO₀ _).mp v.2
  obtain ⟨r, s, hs, hrs⟩ := hsurj _ hvP (hfrac _ (v : F₀).2)
  refine ⟨(r, ⟨s, hs⟩), ?_⟩
  apply Subtype.ext; apply Subtype.ext
  exact hrs

def locEquivRestricted [(cen N P).IsPrime]
    (hfrac : ∀ x : F, x ∈ F₀ → ∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀)
    (hsurj : ∀ x : F, x ∈ P.toValuationSubring → (∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀) →
      ∃ r s : N, s ∉ cen N P ∧ x * s = r) :
    Localization.AtPrime (cen N P) ≃+* O₀ :=
  RingEquiv.ofBijective (locToRestricted N P O₀ hO₀ hN h)
    ⟨locToRestricted_injective N P O₀ hO₀ hN h, locToRestricted_surjective N P O₀ hO₀ hN h hfrac hsurj⟩

include h in

theorem length_localizedModule_cen_eq_ord {K : Type*} [Field K] [Algebra K F₀] (P₀ : Place K F₀)
    (hP₀ : ∀ x : F₀, x ∈ P₀.toValuationSubring ↔ (x : F) ∈ P.toValuationSubring)
    [(cen N P).IsPrime]
    (hfrac : ∀ x : F, x ∈ F₀ → ∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀)
    (hsurj : ∀ x : F, x ∈ P.toValuationSubring → (∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀) →
      ∃ r s : N, s ∉ cen N P ∧ x * s = r)
    (f : N) (hf0 : f ≠ 0) :
    Module.length (Localization.AtPrime (cen N P))
        (LocalizedModule (cen N P).primeCompl (N ⧸ Ideal.span {f})) =
      ((P₀.ord ((⟨(f : F), hN f.2⟩ : F₀) : F₀)).toNat : ℕ∞) := by
  set e := locEquivRestricted N P P₀.toValuationSubring hP₀ hN h hfrac hsurj with he
  rw [length_localizedModule_quotient, Ideal.map_span, Set.image_singleton,
    length_quotient_eq_of_ringEquiv e, Ideal.map_span, Set.image_singleton]
  have hef : e (algebraMap N (Localization.AtPrime (cen N P)) f) =
      toRestricted N P P₀.toValuationSubring hP₀ hN h f :=
    locToRestricted_algebraMap N P P₀.toValuationSubring hP₀ hN h f
  rw [hef, length_quotient_span_eq_ord P₀]
  · rfl
  · intro h0
    exact hf0 (toRestricted_injective N P P₀.toValuationSubring hP₀ hN h (by rw [h0, map_zero]))

end CentreDVR

section ConstantField

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

abbrev KC (C : Subring L) : Subfield L := Subfield.closure (C : Set L)

abbrev FN (N : Subring F) : Subfield F := Subfield.closure (N : Set F)

variable (C : Subring L) (N : Subring F)

theorem algebraMap_mem_FN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) (k : KC C) : algebraMap L F (k : L) ∈ FN N := by
  have hle : KC C ≤ (FN N).comap (algebraMap L F) := by
    rw [Subfield.closure_le]
    intro c hc
    exact Subfield.subset_closure (hCmem c hc)
  exact hle k.2

@[reducible] def algKFN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) : Algebra (KC C) (FN N) :=
  RingHom.toAlgebra ((algebraMap (KC C) F).codRestrict (FN N) (algebraMap_mem_FN C N hCmem))

theorem isScalarTower_KFN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) :
    letI := algKFN C N hCmem; IsScalarTower (KC C) (FN N) F :=
  letI := algKFN C N hCmem
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[reducible] def algCK : Algebra C (KC C) :=
  RingHom.toAlgebra ((C.subtype).codRestrict (KC C) (fun c => Subfield.subset_closure c.2))

theorem isScalarTower_CKL : letI := algCK C; IsScalarTower C (KC C) L :=
  letI := algCK C
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isAlgebraic_KC (A : ValuationSubring L) (halg : ∀ a : L, a ∈ A → IsAlgebraic C a) :
    Algebra.IsAlgebraic (KC C) L := by
  letI := algCK C
  haveI := isScalarTower_CKL C
  have hinj : Function.Injective (algebraMap C (KC C)) := by
    intro a b hab
    have := congrArg (fun z : KC C => (z : L)) hab
    exact Subtype.ext this
  have hA : ∀ a : L, a ∈ A → IsAlgebraic (KC C) a := fun a ha =>
    IsAlgebraic.extendScalars (R := C) (S := KC C) (A := L) hinj (halg a ha)
  refine ⟨fun x => ?_⟩
  rcases A.mem_or_inv_mem x with hx | hx
  · exact hA x hx
  · exact IsAlgebraic.inv_iff.mp (hA _ hx)

theorem exists_fraction_of_mem_FN (x : F) (hx : x ∈ FN N) : ∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  by_cases hz0 : z = 0
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    simp [hz0]
  · refine ⟨⟨y, hy⟩, ⟨z, hz⟩, fun h => hz0 (congrArg Subtype.val h), ?_⟩
    show y / z * z = y
    rw [div_mul_cancel₀ y hz0]

theorem isIntegral_FN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → N) (b : N),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : N) : F)) [Algebra.IsAlgebraic (KC C) L] :
    letI := algKFN C N hCmem; Algebra.IsIntegral (FN N) F := by
  letI := algKFN C N hCmem
  haveI := isScalarTower_KFN C N hCmem
  refine ⟨fun f => ?_⟩
  obtain ⟨n, c, a, b, hb, hfb⟩ := hgen f
  have hconst : ∀ x : L, IsIntegral (FN N) (algebraMap L F x) := fun x => by
    have hK : IsIntegral (KC C) x := (Algebra.IsAlgebraic.isAlgebraic (R := KC C) x).isIntegral
    have hKF : IsIntegral (KC C) (algebraMap L F x) := hK.map (IsScalarTower.toAlgHom (KC C) L F)
    exact hKF.tower_top
  have hsum : IsIntegral (FN N) (f * (b : F)) := by
    rw [hfb]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact (hconst (c i)).mul (isIntegral_algebraMap (R := FN N) (x := (⟨(a i : F), Subfield.subset_closure (a i).2⟩ : FN N)))
  have hbinv : IsIntegral (FN N) ((b : F)⁻¹) :=
    isIntegral_algebraMap (R := FN N) (x := (⟨(b : F)⁻¹, inv_mem (Subfield.subset_closure b.2)⟩ : FN N))
  have : f = f * (b : F) * (b : F)⁻¹ := by rw [mul_inv_cancel_right₀ hb]
  rw [this]
  exact hsum.mul hbinv

theorem adjoin_range_eq_top (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → N) (b : N),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : N) : F)) :
    letI := algKFN C N hCmem; Algebra.adjoin (FN N) (Set.range (algebraMap L F)) = ⊤ := by
  letI := algKFN C N hCmem
  rw [eq_top_iff]
  intro f _
  obtain ⟨n, c, a, b, hb, hfb⟩ := hgen f
  have hmem : f * (b : F) ∈ Algebra.adjoin (FN N) (Set.range (algebraMap L F)) := by
    rw [hfb]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨c i, rfl⟩) ?_
    exact Subalgebra.algebraMap_mem _ (⟨(a i : F), Subfield.subset_closure (a i).2⟩ : FN N)
  have hbinv : (b : F)⁻¹ ∈ Algebra.adjoin (FN N) (Set.range (algebraMap L F)) :=
    Subalgebra.algebraMap_mem _ (⟨(b : F)⁻¹, inv_mem (Subfield.subset_closure b.2)⟩ : FN N)
  have : f = f * (b : F) * (b : F)⁻¹ := by rw [mul_inv_cancel_right₀ hb]
  rw [this]
  exact Subalgebra.mul_mem _ hmem hbinv

theorem mem_range_of_isAlgebraic [IsAlgClosed L] (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (y : FN N) (hy : letI := algKFN C N hCmem; IsAlgebraic (KC C) y) :
    letI := algKFN C N hCmem; y ∈ (algebraMap (KC C) (FN N)).range := by
  letI := algKFN C N hCmem
  haveI := isScalarTower_KFN C N hCmem

  have hyF : IsAlgebraic (KC C) (y : F) := hy.algebraMap
  have hyL : IsAlgebraic L (y : F) :=
    hyF.extendScalars (R := KC C) (S := L) (A := F) (algebraMap (KC C) L).injective
  have hint : IsIntegral L (y : F) := hyL.isIntegral
  obtain ⟨c, hc⟩ : (y : F) ∈ (algebraMap L F).range :=
    minpoly.mem_range_of_degree_eq_one L (y : F)
      (IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint))

  obtain ⟨a, b, hb, hab⟩ := exists_fraction_of_mem_FN N (y : F) y.2
  have hbF : ((b : N) : F) ≠ 0 := fun h => hb (Subtype.ext h)

  have hrel : ∑ i, (![c, -1] : Fin 2 → L) i • (((![b, a] : Fin 2 → N) i : N) : F) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Algebra.smul_def, hc, hab, neg_one_smul, add_neg_cancel]
  have hnotli : ¬ LinearIndependent C (![c, -1] : Fin 2 → L) := by
    intro hli
    have := hld 2 ![c, -1] ![b, a] hli hrel 0
    exact hb (by simpa using this)
  rw [LinearIndependent.pair_iff] at hnotli
  push Not at hnotli
  obtain ⟨s, t, hst, hst0⟩ := hnotli
  have hs0 : (s : L) ≠ 0 := by
    intro hs
    have hsz : s = 0 := Subtype.ext hs
    apply hst0 hsz
    rw [hsz, zero_smul, zero_add, smul_neg, neg_eq_zero, Subring.smul_def, smul_eq_mul, mul_one] at hst
    exact Subtype.ext hst
  have hcK : c ∈ KC C := by
    have hct : c = (t : L) / (s : L) := by
      rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, mul_neg, mul_one] at hst
      field_simp
      linear_combination hst
    rw [hct]
    exact div_mem (Subfield.subset_closure t.2) (Subfield.subset_closure s.2)
  refine ⟨⟨c, hcK⟩, Subtype.ext ?_⟩
  exact hc

end ConstantField

section ResidualA

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {F : Type*} [Field F] [Algebra L F]

theorem exists_place_restrict (A : ValuationSubring L) (C : Subring L) (N : Subring F)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)
    (halg : ∀ a : L, a ∈ A → IsAlgebraic C a)
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → N) (b : N),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : N) : F))
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (P : Place L F) :
    letI := algKFN C N hCmem
    ∃ P₀ : Place (KC C) (FN N),
      (∀ x : FN N, x ∈ P₀.toValuationSubring ↔ (x : F) ∈ P.toValuationSubring) ∧
      ∀ f : N, P.ord (f : F) = P₀.ord ⟨(f : F), Subfield.subset_closure f.2⟩ := by
  letI := algKFN C N hCmem
  haveI := isScalarTower_KFN C N hCmem
  haveI : Algebra.IsAlgebraic (KC C) L := isAlgebraic_KC C A halg
  haveI : Algebra.IsIntegral (FN N) F := isIntegral_FN C N hCmem hgen
  have he := AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
    (K := KC C) (K' := L) (F := FN N) (F' := F) (adjoin_range_eq_top C N hCmem hgen)
    (mem_range_of_isAlgebraic C N hCmem hld) P
  refine ⟨(P.forgetConstants (K := KC C)).restrict (FN N), fun x => Iff.rfl, fun f => ?_⟩
  have h1 := Place.ord_restrict (P.forgetConstants (K := KC C)) (⟨(f : F), Subfield.subset_closure f.2⟩ : FN N)
  rw [he, Nat.cast_one, one_mul] at h1
  exact h1

theorem ordEqLength_of_frame (A : ValuationSubring L) (S : Set (Place L F))
    (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀]
    (hSN : ∀ P ∈ S, ∀ g : F, g ∈ 𝒩₀ → g ∈ P.toValuationSubring)
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → 𝒩₀) (b : 𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : 𝒩₀) : F))
    (C : Subring L) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (halg : ∀ a : L, a ∈ A → IsAlgebraic C a)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → 𝒩₀), LinearIndependent C c →
      ∑ i, c i • ((a i : 𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (ϖN : 𝒩₀) (hϖmax : ϖN ∈ maximalIdeal 𝒩₀) (hϖcen : ∀ P ∈ S, ϖN ∉ cen 𝒩₀ P)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (f : 𝒩₀) (hf0 : f ≠ 0) : OrdEqLength S 𝒩₀ f := by
  intro P hP 𝔭 _ hcen hf𝔭
  subst hcen
  have h := hSN P hP
  letI := algKFN C 𝒩₀ hCmem
  obtain ⟨P₀, hP₀, hordP₀⟩ := exists_place_restrict A C 𝒩₀ hCmem halg hgen hld P

  have hPiff : ∀ b : 𝒩₀, b ∈ cen 𝒩₀ P ↔ 𝒩₀.subtype b ∈ P.toValuationSubring.nonunits := fun b => by
    rw [mem_cen_iff 𝒩₀ P h b, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hPm : cen 𝒩₀ P ≠ maximalIdeal 𝒩₀ := fun heq => hϖcen P hP (heq ▸ hϖmax)
  have hsurj := IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
    π hπ E hE ι 𝒩₀.subtype Subtype.coe_injective P.toValuationSubring (fun b => h b b.2) (cen 𝒩₀ P) hPiff hPm
  have hfrac : ∀ x : F, x ∈ FN 𝒩₀ → ∃ r₀ s₀ : 𝒩₀, s₀ ≠ 0 ∧ x * s₀ = r₀ := exists_fraction_of_mem_FN 𝒩₀
  have key := length_localizedModule_cen_eq_ord 𝒩₀ P (fun g hg => Subfield.subset_closure hg) h P₀ hP₀ hfrac
    (fun x hx hex => hsurj x hx hex) f hf0
  rw [hordP₀ f, key]

end ResidualA

section Dimension

theorem crossingRelation_ne_zero (W : Type*) [CommRing W] [Nontrivial W] (ϖ : W) :
    ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C ϖ) ≠ 0 := by
  classical
  intro h
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)) h
  have hne : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro h0
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h0
    simp at this
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, map_sub,
    MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_C, if_pos rfl, if_neg hne, map_zero] at h1
  simp at h1

theorem ringKrullDim_uvCrossingModel_le_two (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (ϖ : W) :
    ringKrullDim (UVCrossingModel W ϖ) ≤ 2 := by
  have h3 : ringKrullDim (MvPowerSeries (Fin 2) W) = ((2 + 1 : ℕ) : WithBot ℕ∞) :=
    MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing W 2
  have hr : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
      MvPowerSeries.C ϖ) ∈ nonZeroDivisors (MvPowerSeries (Fin 2) W) :=
    mem_nonZeroDivisors_of_ne_zero (crossingRelation_ne_zero W ϖ)
  have key := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [h3] at key
  change ringKrullDim (UVCrossingModel W ϖ) + 1 ≤ _ at key
  generalize hx : ringKrullDim (UVCrossingModel W ϖ) = x at key ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at key
      exact absurd (WithBot.coe_le_coe.mp key) (by simp)
    | coe n =>
      have key' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((2 + 1 : ℕ) : WithBot ℕ∞) := by
        simpa using key
      have : n + 1 ≤ 2 + 1 := by exact_mod_cast key'
      have hn : n ≤ 2 := by omega
      have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (by exact_mod_cast hn)
      simpa using hn'

end Dimension

section Completion

variable {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

theorem exists_sub_of_mem_map (x : AdicCompletion I A) :
    ∃ a : A, x - AdicCompletion.of I A a ∈ I.map (algebraMap A (AdicCompletion I A)) := by
  classical
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I A x
  refine ⟨a 1, ?_⟩
  set y := AdicCompletion.mk I A a - AdicCompletion.of I A (a 1) with hy

  have hval : ∀ n, y.val n = Submodule.Quotient.mk (a n - a 1) := fun n => rfl
  have hker : AdicCompletion.map I (Submodule.mkQ (I : Submodule A A)) y = 0 := by
    ext n
    rw [AdicCompletion.map_val_apply, hval, LinearMap.reduceModIdeal_apply, AdicCompletion.val_zero_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      trivial
    · have h1 : a n - a 1 ∈ I := by
        have := (AdicCompletion.AdicCauchySequence.mk_eq_mk (I := I) hn a)
        rw [Submodule.Quotient.eq] at this
        simpa [pow_one] using this
      have : Submodule.mkQ (I : Submodule A A) (a n - a 1) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h1
      rw [this, Submodule.Quotient.mk_zero]

  have hex := AdicCompletion.map_exact (I := I) (Submodule.injective_subtype (I : Submodule A A))
    (LinearMap.exact_subtype_mkQ (I : Submodule A A)) (Submodule.mkQ_surjective _)
  obtain ⟨z, hz⟩ := (hex y).mp hker

  obtain ⟨w, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I (↥(I : Submodule A A)) z
  rw [← hz]
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Ideal.zero_mem _
  | tmul r i =>
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of, Submodule.subtype_apply]
    have : r • AdicCompletion.of I A (i : A) = r * algebraMap A (AdicCompletion I A) (i : A) := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact Ideal.add_mem _ h₁ h₂

end Completion

section Frame

variable {N : Type*} [CommRing N] [IsLocalRing N] [IsNoetherianRing N]
  {R : Type*} [CommRing R] [IsLocalRing R]
  (ι : AdicCompletion (maximalIdeal N) N ≃+* R)

noncomputable def jmap : N →+* R := ι.toRingHom.comp (algebraMap N (AdicCompletion (maximalIdeal N) N))

omit [IsNoetherianRing N] [IsLocalRing R] in
theorem jmap_apply (x : N) : jmap ι x = ι (algebraMap N _ x) := rfl

omit [IsLocalRing R] in
theorem jmap_injective : Function.Injective (jmap ι) := by
  intro a b hab
  rw [jmap_apply, jmap_apply] at hab
  have h := ι.injective hab
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at h
  exact AdicCompletion.of_injective (maximalIdeal N) N h

omit [IsNoetherianRing N] [IsLocalRing R] in

theorem not_isUnit_jmap {m : N} (hm : m ∈ maximalIdeal N) : ¬ IsUnit (jmap ι m) := by
  intro hu
  have h1 : IsUnit (algebraMap N (AdicCompletion (maximalIdeal N) N) m) := by
    have := hu.map ι.symm
    rwa [jmap_apply, RingEquiv.symm_apply_apply] at this
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal N) 1)
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of] at h2
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h2
  have h0 : Ideal.Quotient.mk (maximalIdeal N ^ 1) m = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact hm
  rw [h0] at h2
  haveI : Nontrivial (N ⧸ maximalIdeal N ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal N).ne_top)
  exact not_isUnit_zero h2

omit [IsNoetherianRing N] in
theorem map_maximalIdeal_le : (maximalIdeal N).map (jmap ι) ≤ maximalIdeal R := by
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal]
  exact not_isUnit_jmap ι hm

omit [IsLocalRing R] in
theorem exists_sub_jmap_mem (r : R) : ∃ a : N, r - jmap ι a ∈ (maximalIdeal N).map (jmap ι) := by
  obtain ⟨a, ha⟩ := exists_sub_of_mem_map (maximalIdeal N) (ι.symm r)
  refine ⟨a, ?_⟩
  have h := Ideal.mem_map_of_mem ι.toRingHom ha
  rw [Ideal.map_map, map_sub] at h
  have h2 : ι.toRingHom (ι.symm r) = r := ι.apply_symm_apply r
  rw [h2] at h
  exact h

theorem map_maximalIdeal_eq : (maximalIdeal N).map (jmap ι) = maximalIdeal R := by
  refine le_antisymm (map_maximalIdeal_le ι) ?_
  intro r hr
  obtain ⟨a, ha⟩ := exists_sub_jmap_mem ι r
  by_cases haunit : IsUnit a
  · exfalso
    have h1 : r - jmap ι a ∈ maximalIdeal R := map_maximalIdeal_le ι ha
    have h2 : jmap ι a ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hr h1
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 (haunit.map _)
  · have ha' : a ∈ maximalIdeal N := (IsLocalRing.mem_maximalIdeal a).mpr haunit
    have h3 : jmap ι a ∈ (maximalIdeal N).map (jmap ι) := Ideal.mem_map_of_mem _ ha'
    have := Ideal.add_mem _ ha h3
    simpa using this

theorem exists_sub_jmap_mem_maximalIdeal (r : R) : ∃ a : N, r - jmap ι a ∈ maximalIdeal R := by
  obtain ⟨a, ha⟩ := exists_sub_jmap_mem ι r
  exact ⟨a, map_maximalIdeal_le ι ha⟩

omit [IsNoetherianRing N] in

theorem comap_maximalIdeal_eq : (maximalIdeal R).comap (jmap ι) = maximalIdeal N := by
  refine le_antisymm ?_ ?_
  · intro a ha
    rw [Ideal.mem_comap] at ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (hu.map _)
  · rw [← Ideal.map_le_iff_le_comap]
    exact map_maximalIdeal_le ι

end Frame

theorem three_le_ringKrullDim_of_chain {R : Type*} [CommRing R] (p₀ p₁ p₂ p₃ : PrimeSpectrum R)
    (h₀₁ : p₀ < p₁) (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) : (3 : WithBot ℕ∞) ≤ ringKrullDim R := by
  let s : LTSeries (PrimeSpectrum R) :=
    (((RelSeries.singleton _ p₀).snoc p₁ (by simpa using h₀₁)).snoc p₂ (by simpa using h₁₂)).snoc p₃
      (by simpa using h₂₃)
  have hs : s.length = 3 := by simp [s]
  have := Order.LTSeries.length_le_krullDim s
  rw [hs] at this
  rw [ringKrullDim]
  exact_mod_cast this

theorem map_eq_maximalIdeal_of_isReduced {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R ≤ 2) (I : Ideal R) (hI0 : I ≠ ⊥) [hred : IsReduced (R ⧸ I)]
    (Q : Ideal R) [hQ : Q.IsPrime] (hIQ : I ≤ Q) (hQm : Q ≠ maximalIdeal R) :
    I.map (algebraMap R (Localization.AtPrime Q)) = maximalIdeal (Localization.AtPrime Q) := by
  classical

  have hmin : ∀ Q' : Ideal R, Q'.IsPrime → I ≤ Q' → Q' ≤ Q → Q' = Q := by
    intro Q' hQ' hIQ' hQ'Q
    by_contra hne
    have hlt : Q' < Q := lt_of_le_of_ne hQ'Q hne
    have hbot : (⊥ : Ideal R) < Q' := by
      rw [bot_lt_iff_ne_bot]
      intro h
      exact hI0 (le_bot_iff.mp (h ▸ hIQ'))
    have hQlt : Q < maximalIdeal R := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) hQm
    have h3 := three_le_ringKrullDim_of_chain (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⟨Q', hQ'⟩ ⟨Q, hQ⟩
      ⟨maximalIdeal R, inferInstance⟩ hbot hlt hQlt
    have h4 : (3 : WithBot ℕ∞) ≤ 2 := h3.trans hdim
    exact absurd h4 (by decide)

  set T := R ⧸ I with hT
  set mk : R →+* T := Ideal.Quotient.mk I with hmk
  have hmk_surj : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker mk ≤ Q := by rw [hmk, Ideal.mk_ker]; exact hIQ
  set Qb : Ideal T := Q.map mk with hQbdef
  haveI hQb : Qb.IsPrime := Ideal.map_isPrime_of_surjective hmk_surj hker
  have hcomapQb : Qb.comap mk = Q := by
    rw [hQbdef, Ideal.comap_map_of_surjective _ hmk_surj, sup_eq_left]
    intro x hx
    exact hker hx
  have hQbmin : ∀ P : Ideal T, P.IsPrime → P ≤ Qb → P = Qb := by
    intro P hP hPQ
    have h1 : P.comap mk = Q := by
      apply hmin _ (Ideal.comap_isPrime mk P)
      · intro x hx
        rw [Ideal.mem_comap, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact P.zero_mem
      · rw [← hcomapQb]
        exact Ideal.comap_mono hPQ
    rw [← Ideal.map_comap_of_surjective mk hmk_surj P, h1]
  have hkill : ∀ x ∈ Qb, ∃ s ∉ Qb, s * x = 0 := by
    intro x hx
    set Tq := Localization.AtPrime Qb with hTq
    have hnil : IsNilpotent (algebraMap T Tq x) := by
      rw [nilpotent_iff_mem_prime]
      intro J hJ
      have hJc : (J.comap (algebraMap T Tq)) ≤ Qb := by
        intro y hy
        by_contra hyQ
        have hu : IsUnit (algebraMap T Tq y) := IsLocalization.map_units Tq (⟨y, hyQ⟩ : Qb.primeCompl)
        exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hy) hu)
      have hJeq := hQbmin _ (Ideal.comap_isPrime _ J) hJc
      have : x ∈ J.comap (algebraMap T Tq) := by rw [hJeq]; exact hx
      exact Ideal.mem_comap.mp this
    have hzero : algebraMap T Tq x = 0 := hnil.eq_zero
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff Qb.primeCompl Tq x).mp hzero
    exact ⟨s, s.2, hs⟩

  set L := Localization.AtPrime Q with hL
  refine le_antisymm ?_ ?_
  · rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIQ
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro q hq
    obtain ⟨s, hs, hsq⟩ := hkill (mk q) (Ideal.mem_map_of_mem _ hq)
    obtain ⟨s₀, rfl⟩ := hmk_surj s
    have hs₀Q : s₀ ∉ Q := fun h => hs (Ideal.mem_map_of_mem _ h)
    have hprod : s₀ * q ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact hsq
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap R L s₀) := IsLocalization.map_units L (⟨s₀, hs₀Q⟩ : Q.primeCompl)
    have hmem : algebraMap R L (s₀ * q) ∈ I.map (algebraMap R L) := Ideal.mem_map_of_mem _ hprod
    rw [map_mul] at hmem
    obtain ⟨u, hu'⟩ := hu
    have : algebraMap R L q = ↑u⁻¹ * (algebraMap R L s₀ * algebraMap R L q) := by
      rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hmem

theorem length_localizedModule_quotient_eq_one {R : Type*} [CommRing R] (I : Ideal R) (Q : Ideal R) [Q.IsPrime]
    (h : I.map (algebraMap R (Localization.AtPrime Q)) = maximalIdeal (Localization.AtPrime Q)) :
    Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ I)) = 1 := by
  set L := Localization.AtPrime Q
  have e : LocalizedModule Q.primeCompl (R ⧸ I) ≃ₗ[L] L ⧸ I.map (algebraMap R L) :=
    (IsLocalizedModule.isBaseChange Q.primeCompl L (LocalizedModule.mkLinearMap Q.primeCompl (R ⧸ I))).equiv.symm ≪≫ₗ
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L I).toLinearEquiv.symm
  rw [e.length_eq, h]
  haveI : IsSimpleModule L (L ⧸ maximalIdeal L) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨maximalIdeal L, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one L _

section FrameLD

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem linearIndependent_coe_of_hld (C : Subring L) (N : Subring F)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    {n : ℕ} (b : Fin n → FN N) (hb : letI := algKFN C N hCmem; LinearIndependent (KC C) b) :
    LinearIndependent L (fun i => ((b i : FN N) : F)) := by
  letI := algKFN C N hCmem
  letI := algCK C
  haveI := isScalarTower_CKL C
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg

  set V : Submodule (KC C) L := Submodule.span (KC C) (Set.range g) with hV
  haveI : FiniteDimensional (KC C) V := FiniteDimensional.span_of_finite _ (Set.finite_range g)
  set r := Module.finrank (KC C) V with hr
  set e := Module.finBasis (KC C) V with he
  have hgV : ∀ i, g i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  set co : Fin n → Fin r → KC C := fun i k => e.repr ⟨g i, hgV i⟩ k with hco

  set b' : Fin n → F := fun i => ((b i : FN N) : F) with hb'
  set e' : Fin r → F := fun k => algebraMap L F ((e k : V) : L) with he'
  set co' : Fin n → Fin r → F := fun i k => algebraMap L F ((co i k : KC C) : L) with hco'
  have hgi : ∀ i, algebraMap L F (g i) = ∑ k, co' i k * e' k := by
    intro i
    have h1 := e.sum_repr ⟨g i, hgV i⟩
    have h2 := congrArg (fun v : V => algebraMap L F (v : L)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hco', he']
    show algebraMap L F (((e.repr ⟨g i, hgV i⟩ k : KC C) : L) * ((e k : V) : L)) = _
    rw [map_mul]

  have hrel : ∑ k, e' k * (∑ i, co' i k * b' i) = 0 := by
    have h1 : ∑ i, g i • b' i = 0 := hg
    simp_rw [Algebra.smul_def, hgi, Finset.sum_mul] at h1
    rw [Finset.sum_comm] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

  set β : Fin r → FN N := fun k => ∑ i, co i k • b i with hβ
  have hβcoe : ∀ k, ((β k : FN N) : F) = ∑ i, co' i k * b' i := by
    intro k
    rw [hβ]
    simp only [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Subfield.coe_mul]
    rfl

  have hfr : ∀ k, ∃ r₀ s₀ : N, s₀ ≠ 0 ∧ ((β k : FN N) : F) * s₀ = r₀ :=
    fun k => exists_fraction_of_mem_FN N _ (β k).2
  choose rr ss hss hrs using hfr
  set sp : N := ∏ k, ss k with hsp
  have hsp0 : (sp : F) ≠ 0 := by
    rw [hsp, SubmonoidClass.coe_finsetProd]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => fun h => hss k (Subtype.ext h)
  set a : Fin r → N := fun k => rr k * ∏ j ∈ Finset.univ.erase k, ss j with ha
  have hacoe : ∀ k, ((a k : N) : F) = ((β k : FN N) : F) * (sp : F) := by
    intro k
    rw [ha, Subring.coe_mul, ← hrs k, hsp, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_finsetProd, mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun j => ((ss j : N) : F)) (Finset.mem_univ k)]

  have heind : LinearIndependent C (fun k => ((e k : V) : L)) := by
    have h1 : LinearIndependent (KC C) (fun k => ((e k : V) : L)) :=
      e.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    refine h1.restrict_scalars ?_
    intro c₁ c₂ h
    have h2 : algebraMap C (KC C) c₁ = algebraMap C (KC C) c₂ := by simpa [Algebra.smul_def] using h
    exact Subtype.ext (congrArg (fun z : KC C => (z : L)) h2)

  have hzero : ∑ k, ((e k : V) : L) • ((a k : N) : F) = 0 := by
    simp_rw [Algebra.smul_def, hacoe, ← mul_assoc, ← Finset.sum_mul]
    simp_rw [hβcoe]
    rw [show (∑ k, algebraMap L F ((e k : V) : L) * ∑ i, co' i k * b' i) = 0 from hrel, zero_mul]
  have ha0 := hld r (fun k => ((e k : V) : L)) a heind hzero

  have hβ0 : ∀ k, β k = 0 := by
    intro k
    have h1 : ((β k : FN N) : F) * (sp : F) = 0 := by rw [← hacoe, ha0 k]; rfl
    have h2 : ((β k : FN N) : F) = 0 := (mul_eq_zero.mp h1).resolve_right hsp0
    exact Subtype.ext h2
  rw [Fintype.linearIndependent_iff] at hb
  have hco0 : ∀ i k, co i k = 0 := fun i k => hb (fun i => co i k) (hβ0 k) i
  intro i
  apply (algebraMap L F).injective
  rw [hgi, map_zero]
  refine Finset.sum_eq_zero fun k _ => ?_
  show algebraMap L F ((co i k : KC C) : L) * e' k = 0
  rw [hco0 i k]
  simp

theorem finite_residueField_place [IsAlgClosed L] [CharZero L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (C : Subring L) (N : Subring F)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (x : N) (hx : Transcendental L (x : F))
    (P₀ : letI := algKFN C N hCmem; Place (KC C) (FN N)) :
    letI := algKFN C N hCmem; Module.Finite (KC C) P₀.ResidueField := by
  letI := algKFN C N hCmem
  haveI := isScalarTower_KFN C N hCmem
  obtain ⟨t, ht, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := L) (F := F)
  haveI := hfd
  haveI hfx : FiniteDimensional L⟮(x : F)⟯ F := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental t hx
  set x₀ : FN N := ⟨x, Subfield.subset_closure x.2⟩ with hx₀
  have hx₀t : Transcendental (KC C) x₀ := by
    intro halg
    apply hx
    have h1 : IsAlgebraic (KC C) ((x₀ : FN N) : F) := halg.algebraMap
    exact h1.extendScalars (algebraMap (KC C) L).injective
  haveI hfx' : FiniteDimensional L⟮algebraMap (FN N) F x₀⟯ F := hfx
  haveI : FiniteDimensional (KC C)⟮x₀⟯ (FN N) :=
    IntermediateField.finiteDimensional_adjoin_of_linearDisjoint_of_transcendental (K₀ := KC C) (L := L)
      (F₀ := FN N) (F := F) (fun n b hb => linearIndependent_coe_of_hld C N hCmem hld b hb) x₀ hx₀t
  have hdeg := AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin (K := KC C) (F := FN N) x₀ hx₀t P₀
  exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)

end FrameLD

section Glue

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem evalAt_eq_zero_iff (P : Place L F) (hP : P.IsRational) {g : F} (hg : g ∈ P.toValuationSubring) :
    P.evalAt g = 0 ↔ (⟨g, hg⟩ : P.toValuationSubring) ∈ maximalIdeal P.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff, ← P.algebraMap_evalAt hP hg]
  constructor
  · intro h; rw [h, map_zero]
  · intro h
    exact (algebraMap L P.ResidueField).injective (by rw [h, map_zero])

theorem isFractionRing_KC (C : Subring L) : letI := algCK C; IsFractionRing C (KC C) := by
  letI := algCK C
  haveI : FaithfulSMul C (KC C) := (faithfulSMul_iff_algebraMap_injective C (KC C)).mpr
    (fun a b h => Subtype.ext (congrArg (fun z : KC C => (z : L)) h))
  refine IsFractionRing.of_field C (KC C) (fun z => ?_)
  obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp z.2
  rw [Subring.closure_eq] at hy hw
  refine ⟨⟨y, hy⟩, ⟨w, hw⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div]
  exact hyw.symm

variable (N : Subring F) (P : Place L F) (h : ∀ g : F, g ∈ N → g ∈ P.toValuationSubring)
  {F₀ : Subfield F} (O₀ : ValuationSubring F₀)
  (hO₀ : ∀ x : F₀, x ∈ O₀ ↔ (x : F) ∈ P.toValuationSubring) (hN : (N : Set F) ⊆ F₀)

include hO₀ in

theorem isUnit_restricted_iff (x : O₀) : IsUnit x ↔ IsUnit (⟨((x : F₀) : F), (hO₀ _).mp x.2⟩ : P.toValuationSubring) := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun z : O₀ => ((z : F₀) : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    refine IsUnit.of_mul_eq_one (b := ⟨((((u⁻¹ : O₀ˣ) : O₀) : F₀) : F), (hO₀ _).mp ((u⁻¹ : O₀ˣ) : O₀).2⟩) (Subtype.ext ?_)
    exact h1
  · rintro ⟨u, hu⟩
    have hx0 : ((x : F₀) : F) ≠ 0 := by
      intro h0
      have : (u : P.toValuationSubring) = 0 := by rw [hu]; exact Subtype.ext h0
      exact u.ne_zero this
    have hinv : (((x : F₀) : F))⁻¹ ∈ P.toValuationSubring := by
      have h1 : ((u⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring).1 = (((x : F₀) : F))⁻¹ := by
        have h0 := congrArg (fun z : P.toValuationSubring => (z : F)) (Units.mul_inv u)
        rw [MulMemClass.coe_mul, hu] at h0
        exact (eq_inv_of_mul_eq_one_right h0)
      rw [← h1]; exact SetLike.coe_mem _
    have hinvF₀ : ((x : F₀))⁻¹ ∈ O₀ := by
      rw [hO₀]; simpa using hinv
    refine IsUnit.of_mul_eq_one (b := ⟨(x : F₀)⁻¹, hinvF₀⟩) (Subtype.ext (Subtype.ext ?_))
    show ((x : F₀) : F) * (((x : F₀))⁻¹ : F₀) = 1
    rw [Subfield.coe_inv, mul_inv_cancel₀ hx0]

include hO₀ in

theorem ker_residue_toRestricted :
    RingHom.ker ((IsLocalRing.residue O₀).comp (toRestricted N P O₀ hO₀ hN h)) = cen N P := by
  ext g
  rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_cen_iff N P h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_restricted_iff P O₀ hO₀]
  rfl

end Glue

section Reduced

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {F : Type*} [Field F] [Algebra L F]

theorem isReduced_quotient_map_cen [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (A : ValuationSubring L) (𝒩₀ : Subring F) [IsLocalRing 𝒩₀] [IsNoetherianRing 𝒩₀]
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → 𝒩₀) (b : 𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : 𝒩₀) : F))
    (C : Subring L) (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    [IsDomain C] [IsDiscreteValuationRing C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic C a)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → 𝒩₀), LinearIndependent C c →
      ∑ i, c i • ((a i : 𝒩₀) : F) = 0 → ∀ i, a i = 0)
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ι : AdicCompletion (maximalIdeal 𝒩₀) 𝒩₀ ≃+* R)
    (P : Place L F) (h : ∀ g : F, g ∈ 𝒩₀ → g ∈ P.toValuationSubring)
    (x : 𝒩₀) (hxcen : x ∈ cen 𝒩₀ P) (hx0 : x ≠ 0) :
    IsReduced (R ⧸ (cen 𝒩₀ P).map (jmap ι)) := by
  classical
  letI := algKFN C 𝒩₀ hCmem
  haveI := isScalarTower_KFN C 𝒩₀ hCmem

  obtain ⟨P₀, hP₀, -⟩ := exists_place_restrict A C 𝒩₀ hCmem halg hgen hld P

  have hxtr : Transcendental L ((x : 𝒩₀) : F) := by
    intro halgx
    obtain ⟨c, hc⟩ : ((x : 𝒩₀) : F) ∈ (algebraMap L F).range :=
      minpoly.mem_range_of_degree_eq_one L _
        (IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible halgx.isIntegral))
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hx0
      apply Subtype.ext
      rw [← hc, map_zero]; rfl
    have hcN : algebraMap L F c ∈ 𝒩₀ := by rw [hc]; exact x.2
    have hnot := algebraMap_not_mem_cen 𝒩₀ P h hc0 hcN
    apply hnot
    have : (⟨algebraMap L F c, hcN⟩ : 𝒩₀) = x := Subtype.ext hc
    rw [this]; exact hxcen
  haveI hfinκ : Module.Finite (KC C) P₀.ResidueField := finite_residueField_place C 𝒩₀ hCmem hld x hxtr P₀

  set O₀ := P₀.toValuationSubring with hO₀def
  have hN : (𝒩₀ : Set F) ⊆ FN 𝒩₀ := fun g hg => Subfield.subset_closure hg
  set toO : 𝒩₀ →+* O₀ := toRestricted 𝒩₀ P O₀ hP₀ hN h with htoO
  letI algNκ : Algebra 𝒩₀ P₀.ResidueField := ((IsLocalRing.residue O₀).comp toO).toAlgebra
  letI algCN : Algebra C 𝒩₀ :=
    (({ toFun := fun c => ⟨algebraMap L F (c : L), hCmem c c.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) } : C →+* 𝒩₀)).toAlgebra
  letI := algCK C
  haveI := isScalarTower_CKL C
  letI algCκ : Algebra C P₀.ResidueField :=
    ((algebraMap (KC C) P₀.ResidueField).comp (algebraMap C (KC C))).toAlgebra
  haveI : IsScalarTower C (KC C) P₀.ResidueField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower C 𝒩₀ P₀.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    show algebraMap (KC C) P₀.ResidueField (algebraMap C (KC C) c) = IsLocalRing.residue O₀ (toO (algebraMap C 𝒩₀ c))
    rw [IsScalarTower.algebraMap_apply (KC C) O₀ P₀.ResidueField]
    show IsLocalRing.residue O₀ _ = IsLocalRing.residue O₀ _
    congr 1
  haveI : IsFractionRing C (KC C) := isFractionRing_KC C
  haveI : CharZero (KC C) := (algebraMap (KC C) L).charZero
  haveI : Algebra.IsSeparable (KC C) P₀.ResidueField := inferInstance

  have hkerκ : RingHom.ker (algebraMap 𝒩₀ P₀.ResidueField) = cen 𝒩₀ P :=
    ker_residue_toRestricted 𝒩₀ P h O₀ hP₀ hN

  obtain ⟨D₁, hD₁fin, -, hD₁loc⟩ :=
    IsDiscreteValuationRing.exists_finite_locallyPrincipalOverring (C := C) (KC C) (κ := P₀.ResidueField) (A := 𝒩₀)
  haveI := hD₁fin
  have hkerD₁ : RingHom.ker (algebraMap 𝒩₀ D₁) = cen 𝒩₀ P := by
    rw [← hkerκ]
    ext g
    simp only [RingHom.mem_ker]
    rw [← Subalgebra.coe_eq_zero (S := D₁), Subalgebra.coe_algebraMap]

  letI algNR : Algebra 𝒩₀ R := (jmap ι).toAlgebra
  haveI : Module.Flat 𝒩₀ R := flat_comp_completion 𝒩₀ ι
  have hmaxR : (maximalIdeal 𝒩₀).map (algebraMap 𝒩₀ R) = maximalIdeal R := map_maximalIdeal_eq ι
  have hresR : ∀ b : R, ∃ a : 𝒩₀, b - algebraMap 𝒩₀ R a ∈ maximalIdeal R :=
    exists_sub_jmap_mem_maximalIdeal ι
  exact IsLocalRing.isReduced_quotient_map_of_flat_of_locallyPrincipalOverring (A := 𝒩₀) (B := R) (D₁ := D₁)
    hmaxR hresR hD₁loc (cen 𝒩₀ P) hkerD₁

end Reduced

end R1AF8D2b

namespace InjAux

open AlgebraicCurve AlgebraicCurve.GaussReduction

variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem evalAt_add_of_mem (v : Place K' F') (hv : v.IsRational) {f g : F'}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg_of_mem (v : Place K' F') (hv : v.IsRational) {f : F'} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem inv_mem_of_evalAt_ne_zero (v : Place K' F') (hv : v.IsRational) {f : F'} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : f⁻¹ ∈ v.toValuationSubring := by
  rcases v.toValuationSubring.mem_or_inv_mem f with hmem | hmem
  ·
    by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
    · obtain ⟨u, hu⟩ := hu
      have hval : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F') = f⁻¹ := by
        have h2 := congrArg (fun w : v.toValuationSubring => (w : F')) u.inv_mul
        rw [hu] at h2
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2
        exact eq_inv_of_mul_eq_one_left h2
      rw [← hval]; exact SetLike.coe_mem _
    · exfalso
      apply h
      have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
        (IsLocalRing.mem_maximalIdeal _).mpr hu
      rw [R1AF8D2b.evalAt_eq_zero_iff v hv hf]
      exact hmax
  · exact hmem

theorem evalAt_inv_of_evalAt_ne_zero (v : Place K' F') (hv : v.IsRational) {f : F'} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf0 : f ≠ 0 := by
    intro h0; apply h; rw [h0]
    have := evalAt_algebraMap_const v hv (0 : K')
    rwa [map_zero] at this
  have hinv := inv_mem_of_evalAt_ne_zero v hv hf h
  have hmul : v.evalAt f⁻¹ * v.evalAt f = 1 := by
    rw [← evalAt_mul_of_mem v hv hinv hf, inv_mul_cancel₀ hf0, v.evalAt_one]
  exact eq_inv_of_mul_eq_one_left hmul

end InjAux

end

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel R1AF8D2b InjAux AlgebraicCurve.GaussReduction in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∉ 𝔭)
    (P P' : Place L F) (hP : P ∈ S) (hP' : P' ∈ S) (hP𝔭 : ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭)
    (h : ∀ g : ↥𝒩₀, P.evalAt (g : F) = P'.evalAt (g : F)) :
    P = P' := by
  classical
  have hSN : ∀ Q ∈ S, ∀ g : F, g ∈ 𝒩₀ → g ∈ Q.toValuationSubring := fun Q hQ => ((hS Q).mp hQ).1
  have hN := hSN P hP
  have hN' := hSN P' hP'
  have hratP := hrat P hP
  have hratP' := hrat P' hP'
  have hP'𝔭 : ∀ g : ↥𝒩₀, P'.evalAt (g : F) = 0 ↔ g ∈ 𝔭 := fun g => by rw [← h g]; exact hP𝔭 g

  have hPiff : ∀ b : ↥𝒩₀, b ∈ 𝔭 ↔ 𝒩₀.subtype b ∈ P.toValuationSubring.nonunits := by
    intro b
    rw [← hP𝔭 b, evalAt_eq_zero_iff P hratP (hN _ b.2), ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hPiff' : ∀ b : ↥𝒩₀, b ∈ 𝔭 ↔ 𝒩₀.subtype b ∈ P'.toValuationSubring.nonunits := by
    intro b
    rw [← hP'𝔭 b, evalAt_eq_zero_iff P' hratP' (hN' _ b.2), ← ValuationSubring.coe_mem_nonunits_iff]
    rfl

  have hϖN : ¬ IsUnit (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv

    obtain ⟨o, ho⟩ := hres w
    obtain ⟨hwA, -⟩ := ((hS P).mp hP).2 _ ho
    have hsplit : (w : F) = ((w - ⟨algebraMap L F (o : L), hCmem o o.2⟩ : ↥𝒩₀) : F) + algebraMap L F (o : L) := by
      push_cast; ring
    have hwval : P.evalAt (w : F) ∈ A := by
      rw [hsplit, evalAt_add_of_mem P hratP (hN _ (w - _).2) (P.algebraMap_mem' _), evalAt_algebraMap_const P hratP]
      exact add_mem hwA (hC o o.2)
    have hprod : (ϖ : L) * P.evalAt (w : F) = 1 := by
      have h1 := congrArg (fun z : ↥𝒩₀ => P.evalAt (z : F)) hw
      simp only [Subring.coe_mul, OneMemClass.coe_one] at h1
      rw [evalAt_mul_of_mem P hratP (P.algebraMap_mem' _) (hN _ w.2), evalAt_algebraMap_const P hratP,
        Place.evalAt_one] at h1
      exact h1
    have hϖunit : IsUnit (⟨(ϖ : L), hC ϖ ϖ.2⟩ : ↥A) :=
      IsUnit.of_mul_eq_one (b := ⟨_, hwval⟩) (Subtype.ext hprod)
    have hres0 : IsLocalRing.residue ↥A ⟨(ϖ : L), hC ϖ ϖ.2⟩ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hϖunit) hres0
  have hϖmax : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∈ maximalIdeal ↥𝒩₀ :=
    (IsLocalRing.mem_maximalIdeal _).mpr hϖN
  have hPm : 𝔭 ≠ maximalIdeal ↥𝒩₀ := fun heq => h𝔭ϖ (heq ▸ hϖmax)

  have hsurj := IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
    π hπ E hE ι 𝒩₀.subtype Subtype.coe_injective P.toValuationSubring (fun b => hN b b.2) 𝔭 hPiff hPm
  have hsurj' := IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
    π hπ E hE ι 𝒩₀.subtype Subtype.coe_injective P'.toValuationSubring (fun b => hN' b b.2) 𝔭 hPiff' hPm
  have htransfer : ∀ (Q Q' : Place L F), Q.IsRational → Q'.IsRational →
      (∀ g : F, g ∈ 𝒩₀ → g ∈ Q.toValuationSubring) → (∀ g : F, g ∈ 𝒩₀ → g ∈ Q'.toValuationSubring) →
      (∀ g : ↥𝒩₀, Q.evalAt (g : F) = Q'.evalAt (g : F)) → (∀ g : ↥𝒩₀, Q'.evalAt (g : F) = 0 ↔ g ∈ 𝔭) →
      (∀ x : F, x ∈ Q.toValuationSubring → (∃ r₀ s₀ : ↥𝒩₀, s₀ ≠ 0 ∧ x * 𝒩₀.subtype s₀ = 𝒩₀.subtype r₀) →
        ∃ r s : ↥𝒩₀, s ∉ 𝔭 ∧ x * 𝒩₀.subtype s = 𝒩₀.subtype r) →
      ∀ x : F, x ∈ FN 𝒩₀ → x ∈ Q.toValuationSubring → x ∈ Q'.toValuationSubring ∧ Q'.evalAt x = Q.evalAt x := by
    intro Q Q' hQ hQ' hQN hQ'N hQQ' hQ'𝔭 hQsurj x hx hxQ
    obtain ⟨r₀, s₀, hs₀, hxs₀⟩ := exists_fraction_of_mem_FN 𝒩₀ x hx
    obtain ⟨r, s, hs, hxs⟩ := hQsurj x hxQ ⟨r₀, s₀, hs₀, hxs₀⟩
    have hsQ' : Q'.evalAt (s : F) ≠ 0 := fun h0 => hs ((hQ'𝔭 s).mp h0)
    have hsQ : Q.evalAt (s : F) ≠ 0 := by rw [hQQ' s]; exact hsQ'
    have hs0 : (s : F) ≠ 0 := by
      intro h0; apply hsQ'
      rw [h0]; have := evalAt_algebraMap_const Q' hQ' (0 : L); rwa [map_zero] at this
    have hxeq : x = (r : F) * ((s : F))⁻¹ := by
      rw [← (show x * (s : F) = (r : F) from hxs), mul_inv_cancel_right₀ hs0]
    have hsinv' : ((s : F))⁻¹ ∈ Q'.toValuationSubring := inv_mem_of_evalAt_ne_zero Q' hQ' (hQ'N _ s.2) hsQ'
    have hsinv : ((s : F))⁻¹ ∈ Q.toValuationSubring := inv_mem_of_evalAt_ne_zero Q hQ (hQN _ s.2) hsQ
    refine ⟨hxeq ▸ mul_mem (hQ'N _ r.2) hsinv', ?_⟩
    rw [hxeq, evalAt_mul_of_mem Q' hQ' (hQ'N _ r.2) hsinv', evalAt_mul_of_mem Q hQ (hQN _ r.2) hsinv,
      evalAt_inv_of_evalAt_ne_zero Q' hQ' (hQ'N _ s.2) hsQ', evalAt_inv_of_evalAt_ne_zero Q hQ (hQN _ s.2) hsQ,
      hQQ' r, hQQ' s]
  have hF0 := htransfer P P' hratP hratP' hN hN' h hP'𝔭 hsurj
  have hF0' := htransfer P' P hratP' hratP hN' hN (fun g => (h g).symm) hP𝔭 hsurj'

  letI := algKFN C 𝒩₀ hCmem
  haveI := isScalarTower_KFN C 𝒩₀ hCmem
  obtain ⟨P₀, hP₀, -⟩ := exists_place_restrict A C 𝒩₀ hCmem halg hgen hld P
  have h₁ : P.toValuationSubring.comap (algebraMap (FN 𝒩₀) F) = P₀.toValuationSubring := by
    ext x; rw [ValuationSubring.mem_comap]; exact (hP₀ x).symm
  have h₂ : P'.toValuationSubring.comap (algebraMap (FN 𝒩₀) F) = P₀.toValuationSubring := by
    ext x; rw [ValuationSubring.mem_comap, hP₀]
    exact ⟨fun hx => (hF0' x x.2 hx).1, fun hx => (hF0 x x.2 hx).1⟩

  haveI : Algebra.IsAlgebraic (KC C) L := isAlgebraic_KC C A halg
  haveI : CharZero (KC C) := (algebraMap (KC C) L).charZero
  haveI : PerfectField (KC C) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable (KC C) L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsIntegral (FN 𝒩₀) F := isIntegral_FN C 𝒩₀ hCmem hgen

  have hagree : ∀ x ∈ Subring.closure
      ((algebraMap (FN 𝒩₀) F) '' (P₀.toValuationSubring : Set (FN 𝒩₀)) ∪ Set.range (algebraMap L F)),
      x ∈ P.toValuationSubring ∧ x ∈ P'.toValuationSubring ∧ P.evalAt x = P'.evalAt x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨z, hz, rfl⟩ | ⟨l, rfl⟩
      · have hzP : (z : F) ∈ P.toValuationSubring := (hP₀ z).mp hz
        obtain ⟨hzP', hval⟩ := hF0 z z.2 hzP
        exact ⟨hzP, hzP', hval.symm⟩
      · exact ⟨P.algebraMap_mem' l, P'.algebraMap_mem' l,
          by rw [evalAt_algebraMap_const P hratP, evalAt_algebraMap_const P' hratP']⟩
    | zero => exact ⟨zero_mem _, zero_mem _, by
        have h0 := evalAt_algebraMap_const P hratP (0 : L); have h0' := evalAt_algebraMap_const P' hratP' (0 : L)
        rw [map_zero] at h0 h0'; rw [h0, h0']⟩
    | one => exact ⟨one_mem _, one_mem _, by rw [Place.evalAt_one, Place.evalAt_one]⟩
    | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, add_mem ha.2.1 hb.2.1, by
        rw [evalAt_add_of_mem P hratP ha.1 hb.1, evalAt_add_of_mem P' hratP' ha.2.1 hb.2.1, ha.2.2, hb.2.2]⟩
    | neg a _ ha => exact ⟨neg_mem ha.1, neg_mem ha.2.1, by
        rw [evalAt_neg_of_mem P hratP ha.1, evalAt_neg_of_mem P' hratP' ha.2.1, ha.2.2]⟩
    | mul a b _ _ ha hb => exact ⟨mul_mem ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by
        rw [evalAt_mul_of_mem P hratP ha.1 hb.1, evalAt_mul_of_mem P' hratP' ha.2.1 hb.2.1, ha.2.2, hb.2.2]⟩
  have hc : ∀ x ∈ Subring.closure
      ((algebraMap (FN 𝒩₀) F) '' (P₀.toValuationSubring : Set (FN 𝒩₀)) ∪ Set.range (algebraMap L F)),
      x ∈ P.toValuationSubring.nonunits ↔ x ∈ P'.toValuationSubring.nonunits := by
    intro x hx
    obtain ⟨hxP, hxP', hval⟩ := hagree x hx
    rw [show x = ((⟨x, hxP⟩ : P.toValuationSubring) : F) from rfl, ValuationSubring.coe_mem_nonunits_iff,
      ← evalAt_eq_zero_iff P hratP hxP, hval, evalAt_eq_zero_iff P' hratP' hxP',
      ← ValuationSubring.coe_mem_nonunits_iff]
  exact AlgebraicCurve.Place.eq_of_comap_eq_of_forall_mem_nonunits_iff (κ := KC C) (F := FN 𝒩₀) (κ' := L) (F' := F)
    (adjoin_range_eq_top C 𝒩₀ hCmem hgen) P₀ P P' h₁ h₂ hc

end S_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_eq_of_forall_evalAt_eq_of_forall_iff_evalAt_eq_zero (solution)
