-- Prove2me | solution 1 for AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7320e7a7-1cca-56a2-b7e5-99cf57a7637a

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_zero_of_forall_isOrbitalIntegralOn_eq_zero
import Theorems.Thm_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
import Theorems.Thm_NumberField_finsum_setIntegral_range_idelicNorm_comp_mul_eq_setIntegral_principalIdeles_sup_range_of_prime
import Theorems.Thm_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Theorems.Thm_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
import Theorems.Thm_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar LT.TwistedNorm
open scoped TensorProduct

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "centralCell ellipticCell mem_ellipticCell_iff glBorelOf centralizerBorel toTensorGL normString IsOrbitalIntegralOn AreMatchingOn AdelicGL2 globalPoints centralScalar sigmaAdelicAct sigmaCentralizer continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_zero_of_forall_isOrbitalIntegralOn_eq_zero exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport"
namespace C4Assembly
p2m_open "AutomorphicForm"

section Fibres

open Function

theorem finsum_mem_eq_finsum_mem_fibres {ι κ M : Type*} [AddCommMonoid M]
    (S : Set ι) (G : Set κ) (r : ι → κ) (Fam : κ → Set ι) (w : ι → M)
    (hfin : (S ∩ support w).Finite)
    (h1 : ∀ δ ∈ S, r δ ∈ G ∧ δ ∈ Fam (r δ))
    (h2 : ∀ γ ∈ G, ∀ δ ∈ Fam γ, δ ∈ S ∧ r δ = γ) :
    ∑ᶠ δ ∈ S, w δ = ∑ᶠ γ ∈ G, ∑ᶠ δ ∈ Fam γ, w δ := by
  classical
  set s : Finset ι := hfin.toFinset with hs

  have hL : ∑ᶠ δ ∈ S, w δ = ∑ δ ∈ s, w δ := by
    refine finsum_mem_eq_sum_of_subset w ?_ ?_
    · intro δ hδ; rw [hs, Set.Finite.coe_toFinset]; exact hδ
    · intro δ hδ; rw [hs, Set.Finite.coe_toFinset] at hδ; exact hδ.1

  have hF : ∀ γ ∈ G, ∑ᶠ δ ∈ Fam γ, w δ = ∑ δ ∈ s with r δ = γ, w δ := by
    intro γ hγ
    refine finsum_mem_eq_sum_of_subset w ?_ ?_
    · rintro δ ⟨hδ, hw⟩
      obtain ⟨hδS, hr⟩ := h2 γ hγ δ hδ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hs, Set.Finite.mem_toFinset]
      exact ⟨⟨hδS, hw⟩, hr⟩
    · intro δ hδ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hs, Set.Finite.mem_toFinset] at hδ
      obtain ⟨⟨hδS, -⟩, hr⟩ := hδ
      rw [← hr]
      exact (h1 δ hδS).2

  have hO : ∑ᶠ γ ∈ G, ∑ᶠ δ ∈ Fam γ, w δ = ∑ γ ∈ s.image r, ∑ᶠ δ ∈ Fam γ, w δ := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro γ ⟨hγ, hne⟩
      rw [Function.mem_support, hF γ hγ] at hne
      obtain ⟨δ, hδ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      simp only [Finset.mem_filter] at hδ
      simp only [Finset.coe_image]
      exact ⟨δ, hδ.1, hδ.2⟩
    · intro γ hγ
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hs, Set.Finite.mem_toFinset] at hγ
      obtain ⟨δ, ⟨hδS, -⟩, rfl⟩ := hγ
      exact (h1 δ hδS).1
  rw [hL, hO]
  have himg : ∀ γ ∈ s.image r, γ ∈ G := by
    intro γ hγ
    simp only [Finset.mem_image, hs, Set.Finite.mem_toFinset] at hγ
    obtain ⟨δ, ⟨hδS, -⟩, rfl⟩ := hγ
    exact (h1 δ hδS).1
  rw [Finset.sum_congr rfl fun γ hγ => hF γ (himg γ hγ)]
  exact (Finset.sum_fiberwise_of_maps_to (fun δ hδ => Finset.mem_image_of_mem r hδ) w).symm

theorem finsum_mem_finset_sum_comm {α β M : Type*} [AddCommMonoid M] (G : Set α) (s : Finset β)
    (g : β → α → M) (hfin : ∀ b ∈ s, (G ∩ support (g b)).Finite) :
    ∑ᶠ a ∈ G, ∑ b ∈ s, g b a = ∑ b ∈ s, ∑ᶠ a ∈ G, g b a := by
  classical
  set sT : Set α := G ∩ ⋃ b ∈ s, support (g b) with hsT
  have hsTfin : sT.Finite := by
    rw [hsT, Set.inter_iUnion₂]
    exact s.finite_toSet.biUnion fun b hb => hfin b (Finset.mem_coe.mp hb)
  have hsub : G ∩ support (fun a => ∑ b ∈ s, g b a) ⊆ sT := by
    rintro a ⟨haG, hne⟩
    rw [mem_support] at hne
    obtain ⟨b, hb, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨haG, Set.mem_biUnion (Finset.mem_coe.mpr hb) hne'⟩
  have h1 : ∑ᶠ a ∈ G, ∑ b ∈ s, g b a = ∑ a ∈ hsTfin.toFinset, ∑ b ∈ s, g b a := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · intro a ha; rw [Set.Finite.coe_toFinset]; exact hsub ha
    · intro a ha; rw [Set.Finite.coe_toFinset] at ha; exact ha.1
  have h2 : ∀ b ∈ s, ∑ᶠ a ∈ G, g b a = ∑ a ∈ hsTfin.toFinset, g b a := by
    intro b hb
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro a ⟨haG, hne⟩
      rw [Set.Finite.coe_toFinset]
      exact ⟨haG, Set.mem_biUnion (Finset.mem_coe.mpr hb) hne⟩
    · intro a ha; rw [Set.Finite.coe_toFinset] at ha; exact ha.1
  rw [h1, Finset.sum_comm]
  exact (Finset.sum_congr rfl h2).symm

end Fibres

section GL2

variable {K : Type*} [Field K]

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem scalar_mul_comm (c : Kˣ) (g : GL (Fin 2) K) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : K) * (g : Matrix (Fin 2) (Fin 2) K) =
    (g : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (c : K)
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) _).eq

theorem conj_scalar_mul (c : Kˣ) (g h : GL (Fin 2) K) :
    h⁻¹ * (sc c * g) * h = sc c * (h⁻¹ * g * h) := by
  rw [show h⁻¹ * (sc c * g) * h = (h⁻¹ * sc c) * (g * h) by simp only [mul_assoc],
    ← scalar_mul_comm c h⁻¹]
  simp only [mul_assoc]

theorem scalar_mul_mem_ellipticCell (a : Kˣ) {γ : GL (Fin 2) K}
    (hγ : γ ∈ AutomorphicForm.ellipticCell K) :
    sc a * γ ∈ AutomorphicForm.ellipticCell K := by
  rw [AutomorphicForm.mem_ellipticCell_iff] at hγ ⊢
  intro r hr
  apply hγ (r / a)
  have hval : ((sc a * γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (a : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    simp [Matrix.diagonal_mul]
  rw [hval] at hr
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hr ⊢
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin,
    smul_eq_mul] at hr ⊢
  have ha : (a : K) ≠ 0 := a.ne_zero
  have key : (r / a) ^ 2 - Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) * (r / a) +
      Matrix.det (γ : Matrix (Fin 2) (Fin 2) K) =
      (r ^ 2 - (a : K) * Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) * r +
        (a : K) ^ 2 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) K)) / (a : K) ^ 2 := by
    field_simp
  rw [key, hr, zero_div]

theorem conj_mem_ellipticCell {γ : GL (Fin 2) K} (hγ : γ ∈ AutomorphicForm.ellipticCell K) (h : GL (Fin 2) K) :
    h⁻¹ * γ * h ∈ AutomorphicForm.ellipticCell K := by
  intro a
  have hc : ((h⁻¹ * γ * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' h γ
  rw [hc]
  exact hγ a

theorem mk_scalar_mul_conj (a : Kˣ) (γ h : GL (Fin 2) K) :
    ConjClasses.mk (sc a * (h⁻¹ * γ * h)) = ConjClasses.mk (sc a * γ) := by
  rw [← conj_scalar_mul, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  exact ⟨h, by group⟩

end GL2

section NormScalar

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

omit [FiniteDimensional F L] [IsGalois F L] in
theorem map_scalar (u : Lˣ) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (sc u) = sc (Units.map ((σ : L →+* L) : L →* L) u) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

omit [FiniteDimensional F L] [IsGalois F L] in
theorem sigmaPartialNorm_scalar_mul (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (sc u * δ) r =
      sc (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) u r) *
        sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul, map_scalar,
        map_mul]
      rw [← mul_assoc, mul_assoc (sc u) δ, ← scalar_mul_comm, ← mul_assoc, ← map_mul, mul_assoc]

theorem map_algebraMap_scalar_norm (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap F L) (sc (Units.map (Algebra.norm F : L →* F) u)) =
      sc (sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Module.finrank F L) u) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Units.coe_map]
    rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  · simp [hij]

theorem isNormRep_scalar_mul (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (u : Lˣ) :
    IsNormRep σ (sc (Units.map (Algebra.norm F : L →* F) u) * γ) (sc u * δ) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_def, sigmaPartialNorm_scalar_mul, ← sigmaNormPow_def, ← sigmaNormPow_def, map_mul,
    map_algebraMap_scalar_norm hgen, ← hP, ← conj_scalar_mul]

theorem isNormRep_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) c⁻¹, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, ← hP]
  group

theorem normClassMap_scalar_mul (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (u : Lˣ) :
    normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ)) =
      ConjClasses.mk (sc (Units.map (Algebra.norm F : L →* F) u) * γ) :=
  normClassMap_mk_eq_of_isNormRep hgen (isNormRep_scalar_mul hgen (isNormRep_of_normClassMap_eq hgen h) u)

theorem normClassMap_mk_sigmaConj (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ h : GL (Fin 2) L) :
    normClassMap hgen (SigmaConjClasses.mk σ (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) =
      normClassMap hgen (SigmaConjClasses.mk σ δ) := by
  congr 1
  exact (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, rfl⟩).symm

theorem normClassMap_family (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (k : GL (Fin 2) L) (u : Lˣ) :
    normClassMap hgen (SigmaConjClasses.mk σ
        (sc u * (k⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) k))) =
      ConjClasses.mk (sc (Units.map (Algebra.norm F : L →* F) u) * γ) := by
  apply normClassMap_scalar_mul hgen
  rw [normClassMap_mk_sigmaConj]
  exact h

end NormScalar

section KSide

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

def slabO (γ₀ : GL (Fin 2) K) (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (z : (AdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
    (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)

theorem slabO_apply (γ₀ : GL (Fin 2) K) (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    slabO K γ₀ Ψ f z = ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := rfl

theorem setIntegral_subgroup_mul_left {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (hH : MeasurableSet (H : Set G))
    {m : G} (hm : m ∈ H) (g : G → ℂ) :
    ∫ u in (H : Set G), g (m * u) ∂μ = ∫ u in (H : Set G), g u ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have hind : (H : Set G).indicator (fun u => g (m * u)) = fun u => (H : Set G).indicator g (m * u) := by
    funext u
    by_cases hu : u ∈ (H : Set G)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (H.mul_mem hm hu)]
    · have hmu : m * u ∉ (H : Set G) := fun h => hu (by simpa using H.mul_mem (H.inv_mem hm) h)
      rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hmu]
  rw [hind]
  exact integral_mul_left_eq_self _ m

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem slabO_eq_zero_of_not_isNormClass
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β : ℝ) (hα : 0 < α)
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hvan : ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      ¬ LT.TwistedNorm.IsNormClass hgen
          (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u)) →
      ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          τ f I → I = 0)
    (a : Kˣ) (ha : ¬ LT.TwistedNorm.IsNormClass hgen
      (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (hu : u ∈ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) :
    slabO K γ₀ Ψ f (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u) = 0 := by
  have hc := AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_mem_range_idelicNorm
    K L σ hgen u hu
  exact AutomorphicForm.setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_zero_of_forall_isOrbitalIntegralOn_eq_zero
    K α β hα γ₀ hγ₀ Ψ hΨs hΨ f hf hfc _ (hvan a u ha hc)

theorem sum_integral_eq_finsum_sum_setIntegral
    (hprime : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (T : Set Kˣ)
    (hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b)
    (α β : ℝ) (hα : 0 < α)
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (T ∩ Function.support (fun t : Kˣ => ∑ ξK ∈ Ξ,
        ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
          ((ξK ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t * u,
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            slabO K γ₀ Ψ f (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t * u)
          ∂νZK)).Finite ∧
    ∑ᶠ t ∈ T, ∑ ξK ∈ Ξ,
        ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
          ((ξK ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t * u,
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            slabO K γ₀ Ψ f (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t * u)
          ∂νZK =
      ∑ ξK ∈ Ξ, ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * slabO K γ₀ Ψ f z ∂νZK := by
  classical

  obtain ⟨hOc, hOs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_setIntegral_fundamentalDomain_conj_centralScalar_mul_of_mem_ellipticCell
      K α β hα γ₀ hγ₀ Ψ hΨs hΨ f hf hfc
  change Continuous (slabO K γ₀ Ψ f) at hOc
  change HasCompactSupport (slabO K γ₀ Ψ f) at hOs

  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hN
  set ι : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
    with hι
  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    ((M4aHerbrand.principalIdeles (𝓞 K) K ⊔ N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)
    with hU

  set G : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    fun ξ z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * slabO K γ₀ Ψ f z with hG
  have hGc : ∀ ξ ∈ Ξ, Continuous (G ξ) := fun ξ hξ => ((hΞ ξ).1 hξ).1.mul hOc
  have hGs : ∀ ξ ∈ Ξ, HasCompactSupport (G ξ) := fun ξ _ => hOs.mul_left
  have hGi : ∀ ξ ∈ Ξ, Integrable (G ξ) νZK := fun ξ hξ => (hGc ξ hξ).integrable_of_hasCompactSupport (hGs ξ hξ)

  have h108 : ∀ ξ ∈ Ξ,
      (T ∩ Function.support (fun t : Kˣ => ∫ u in Set.range N, G ξ (ι t * u) ∂νZK)).Finite ∧
      ∑ᶠ t ∈ T, ∫ u in Set.range N, G ξ (ι t * u) ∂νZK = ∫ u in U, G ξ u ∂νZK := fun ξ hξ =>
    NumberField.finsum_setIntegral_range_idelicNorm_comp_mul_eq_setIntegral_principalIdeles_sup_range_of_prime
      K L hprime σ hgen νZK T hT (G ξ) (hGi ξ hξ) (hGs ξ hξ)

  set sT : Set Kˣ := T ∩ ⋃ ξ ∈ Ξ, Function.support (fun t : Kˣ => ∫ u in Set.range N, G ξ (ι t * u) ∂νZK)
    with hsT
  have hsTfin : sT.Finite := by
    rw [hsT, Set.inter_iUnion₂]
    exact Ξ.finite_toSet.biUnion fun ξ hξ => (h108 ξ (Finset.mem_coe.mp hξ)).1
  have hsub : T ∩ Function.support (fun t : Kˣ => ∑ ξK ∈ Ξ, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK) ⊆ sT := by
    rintro t ⟨htT, hne⟩
    rw [Function.mem_support] at hne
    obtain ⟨ξ, hξ, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨htT, Set.mem_biUnion (Finset.mem_coe.mpr hξ) hne'⟩
  refine ⟨hsTfin.subset hsub, ?_⟩
  ·

    have hswap : ∑ᶠ t ∈ T, ∑ ξK ∈ Ξ, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK =
        ∑ ξK ∈ Ξ, ∑ᶠ t ∈ T, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK := by
      have h1 : ∑ᶠ t ∈ T, ∑ ξK ∈ Ξ, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK =
          ∑ t ∈ hsTfin.toFinset, ∑ ξK ∈ Ξ, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK := by
        refine finsum_mem_eq_sum_of_subset _ ?_ ?_
        · intro t ht; rw [Set.Finite.coe_toFinset]; exact hsub ht
        · intro t ht; rw [Set.Finite.coe_toFinset] at ht; exact ht.1
      have h2 : ∀ ξK ∈ Ξ, ∑ᶠ t ∈ T, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK =
          ∑ t ∈ hsTfin.toFinset, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK := by
        intro ξ hξ
        refine finsum_mem_eq_sum_of_subset _ ?_ ?_
        · rintro t ⟨htT, hne⟩
          rw [Set.Finite.coe_toFinset]
          exact ⟨htT, Set.mem_biUnion (Finset.mem_coe.mpr hξ) hne⟩
        · intro t ht; rw [Set.Finite.coe_toFinset] at ht; exact ht.1
      rw [h1, Finset.sum_comm]
      exact (Finset.sum_congr rfl h2).symm

    have hcos : ∑ ξK ∈ Ξ, ∑ᶠ t ∈ T, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK =
        ∑ ξK ∈ Ξ, ∫ u in U, G ξK u ∂νZK :=
      Finset.sum_congr rfl fun ξ hξ => (h108 ξ hξ).2

    obtain ⟨-, hoff, -⟩ := NumberField.sum_ideleClassChar_eq_of_comp_idelicNorm_eq K L ξL Ξ hΞ
    have hfull : ∑ ξK ∈ Ξ, ∫ z, G ξK z ∂νZK = ∑ ξK ∈ Ξ, ∫ u in U, G ξK u ∂νZK := by
      rw [← integral_finsetSum Ξ fun ξ hξ => hGi ξ hξ,
        ← integral_finsetSum Ξ fun ξ hξ => (hGi ξ hξ).integrableOn]
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
      have h0 := hoff z (by
        intro hz'
        apply hz
        rw [hU]
        exact hz')
      show ∑ ξK ∈ Ξ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * slabO K γ₀ Ψ f z = 0
      rw [← Finset.sum_mul, h0, zero_mul]
    show ∑ᶠ t ∈ T, ∑ ξK ∈ Ξ, ∫ u in Set.range N, G ξK (ι t * u) ∂νZK = ∑ ξK ∈ Ξ, ∫ z, G ξK z ∂νZK
    rw [hswap, hcos, hfull]

omit [FiniteDimensional K L] [IsGalois K L] in

theorem setIntegral_range_idelicNorm_mul_norm
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (g : (AdeleRing (𝓞 K) K)ˣ → ℂ) (b : Lˣ)
    (hNb : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
        (Units.map (Algebra.norm K : L →* K) b) ∈
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range) :
    ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
        g (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (Units.map (Algebra.norm K : L →* K) b) * u) ∂νZK =
      ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK := by
  have hopen := NumberField.isOpen_range_idelicNorm K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
  have hmeas : MeasurableSet
      (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range :
        Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := hopen.measurableSet
  have hrange : Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm =
      (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range :
        Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := rfl
  rw [hrange]
  exact setIntegral_subgroup_mul_left νZK _ hmeas hNb g

end KSide

end AutomorphicForm.C4Assembly

end

open IsDedekindDomain NumberField.AdelicLevel
open scoped ENNReal TensorProduct.RightActions
open _root_.AutomorphicForm (AdelicGL2)

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

set_option linter.unusedVariables false in
open AutomorphicForm.C4Assembly in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (RL : Set (GL (Fin 2) L))
    (hRLsub : RL ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ})
    (hRL : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ RL ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h))
    (ΨL : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨLs : ∀ δ₀ ∈ RL, ΨL δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨL : ∀ δ₀ ∈ RL, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (ΨL δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (RK : Set (GL (Fin 2) K))
    (hRKsub : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (ΨK : GL (Fin 2) K → Set (AdelicGL2 (𝓞 K) K))
    (hΨKs : ∀ γ₀ ∈ RK, ΨK γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨK : ∀ γ₀ ∈ RK, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K))
      (ΨK γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (c₀ : NNReal) (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hOn : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
        (adelicGLHaar (Fin 2) (𝓞 L) L))
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
      f)
    (hvan : ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      ¬ LT.TwistedNorm.IsNormClass hgen
          (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u)) →
      ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          τ f I → I = 0)
    (hper : ∀ δ₀ ∈ RL, ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ a : Kˣ,
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) →
      ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL =
        (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) *
          ∑ ξK ∈ Ξ, ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
            ((ξK ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u,
                Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K
                  (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u) * x))
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK) :
    (RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ} ∩
      Function.support (fun δ₀ : GL (Fin 2) L =>
        ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
            ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
              Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
                h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL)).Finite ∧
    (∀ ξK ∈ Ξ, (RK ∩ AutomorphicForm.ellipticCell K ∩
      Function.support (fun γ₀ : GL (Fin 2) K =>
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
          ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK)).Finite) ∧
    (∑ᶠ δ₀ ∈ RL ∩ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk γ},
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ *
        ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL) =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) *
        ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.ellipticCell K,
          ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
              Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
            ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK := by
  classical

  set ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) with hιK
  set Nid := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNid
  set Cst : ℂ := (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) with hCst

  set SL : Set (GL (Fin 2) L) := {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.ellipticCell K ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ}
    with hSL
  set Splus : Set (GL (Fin 2) L) := {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
      (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ}
    with hSplus

  set Fam : GL (Fin 2) K → Set (GL (Fin 2) L) := fun γ₀ => RL ∩ {δ : GL (Fin 2) L | ∃ a : Kˣ,
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)} with hFam

  set eL : GL (Fin 2) L → ℂ := fun δ₀ =>
    ((Nat.card {q : Lˣ ⧸ (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
        ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
          Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
            h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h} : ℕ) : ℂ)⁻¹ with heL
  set eK : GL (Fin 2) K → ℂ := fun γ₀ =>
    ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
        Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ with heK
  set J : GL (Fin 2) L → ℂ := fun δ₀ =>
    ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL with hJ
  set IK : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → GL (Fin 2) K → ℂ := fun ξK γ₀ =>
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * slabO K γ₀ (ΨK γ₀) f z ∂νZK
    with hIK

  have hfinL := AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
    K L σ.symm hgen D φ hφc RL hRLsub hRL
  have F1 : (RL ∩ SL ∩ Function.support (fun δ₀ => eL δ₀ * J δ₀)).Finite := by
    refine hfinL.subset ?_
    rintro δ₀ ⟨⟨hδR, -⟩, hne⟩
    refine ⟨hδR, ?_⟩
    by_contra hall
    push Not at hall
    apply hne
    show eL δ₀ * J δ₀ = 0
    simp only [hJ, hall, integral_zero, mul_zero]
  have hfinK := AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
    K f hfc RK hRKsub hRK
  have F2 : ∀ ξK ∈ Ξ, (RK ∩ AutomorphicForm.ellipticCell K ∩
      Function.support (fun γ₀ => eK γ₀ * IK ξK γ₀)).Finite := by
    intro ξK _
    refine hfinK.subset ?_
    rintro γ₀ ⟨⟨hγR, -⟩, hne⟩
    refine ⟨hγR, ?_⟩
    by_contra hall
    push Not at hall
    apply hne
    show eK γ₀ * IK ξK γ₀ = 0
    simp only [hIK, slabO, hall, integral_zero, mul_zero]
  refine ⟨F1, F2, ?_⟩

  set 𝒩 : Subgroup Kˣ := (Units.map (Algebra.norm K : L →* K)).range with h𝒩
  set T : Set Kˣ := Set.range (fun q : Kˣ ⧸ 𝒩 => Quotient.out q) with hTdef
  have hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b := by
    intro a
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul 𝒩 a
    obtain ⟨b, hb⟩ := n.2
    refine ⟨Quotient.out (QuotientGroup.mk a : Kˣ ⧸ 𝒩), ⟨⟨_, rfl⟩, b⁻¹, ?_⟩, ?_⟩
    · rw [hn, map_inv, hb, mul_inv_cancel_right]
    · rintro t ⟨⟨q, rfl⟩, b', hb'⟩
      have hq : (QuotientGroup.mk a : Kˣ ⧸ 𝒩) = q := by
        rw [← QuotientGroup.out_eq' q]
        refine QuotientGroup.eq.mpr ?_
        rw [hb', mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact 𝒩.inv_mem ⟨b', rfl⟩
      rw [hq]

  have hRKuniq : ∀ γ₀ ∈ RK, ∀ γ₁ ∈ RK, γ₀ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K →
      (∃ (h : GL (Fin 2) K) (a : Kˣ), γ₀ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₁ * h)) →
      γ₁ = γ₀ := by
    intro γ₀ hγ₀ γ₁ hγ₁ hcell hex
    obtain ⟨g, -, huniq⟩ := hRK γ₀ hcell
    have e0 : γ₀ = g := huniq γ₀ ⟨hγ₀, 1, 1, by simp⟩
    have e1 : γ₁ = g := huniq γ₁ ⟨hγ₁, hex⟩
    rw [e0, e1]

  have hrk : ∀ δ : GL (Fin 2) L, δ ∈ SL → ∃ γ₀ : GL (Fin 2) K, (γ₀ ∈ RK ∩ AutomorphicForm.ellipticCell K) ∧
      ∃ a : Kˣ, LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) := by
    rintro δ ⟨γ, hγe, hN⟩
    obtain ⟨γ₀, ⟨hγ₀R, h, a, hγ⟩, -⟩ := hRK γ (Or.inr hγe)
    refine ⟨γ₀, ⟨hγ₀R, ?_⟩, a, ?_⟩
    · have e : γ₀ = (h⁻¹)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * γ) * h⁻¹ := by
        rw [hγ, ← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹), ← map_mul, inv_mul_cancel,
          map_one, one_mul, inv_inv]
        group
      rw [e]
      exact conj_mem_ellipticCell (scalar_mul_mem_ellipticCell a⁻¹ hγe) h⁻¹
    · rw [hN, hγ, mk_scalar_mul_conj]
  choose! rk hrk_mem hrk_a using hrk
  have hpart := finsum_mem_eq_finsum_mem_fibres (RL ∩ SL) (RK ∩ AutomorphicForm.ellipticCell K) rk Fam
    (fun δ₀ => eL δ₀ * J δ₀) F1
    (by
      rintro δ ⟨hδR, hδS⟩
      exact ⟨hrk_mem δ hδS, hδR, hrk_a δ hδS⟩)
    (by
      rintro γ₀ ⟨hγ₀R, hγ₀e⟩ δ ⟨hδR, a, ha⟩
      have hδS : δ ∈ SL := ⟨_, scalar_mul_mem_ellipticCell a hγ₀e, ha⟩
      refine ⟨⟨hδR, hδS⟩, ?_⟩
      obtain ⟨a', ha'⟩ := hrk_a δ hδS
      have hcls : ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a' * rk δ) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) := by rw [← ha', ← ha]
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hcls
      obtain ⟨c, hc⟩ := hcls
      refine hRKuniq γ₀ hγ₀R (rk δ) (hrk_mem δ hδS).1 (Or.inr hγ₀e) ⟨c⁻¹, a⁻¹ * a', ?_⟩
      have e1 : Matrix.GeneralLinearGroup.scalar (Fin 2) a' * (c * rk δ * c⁻¹) =
          c * (Matrix.GeneralLinearGroup.scalar (Fin 2) a' * rk δ) * c⁻¹ := by
        have := conj_scalar_mul a' (rk δ) c⁻¹
        simp only [inv_inv] at this
        exact this.symm
      rw [inv_inv, map_mul, mul_assoc, e1, hc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul])

  have hclass : ∀ γ₀ ∈ RK ∩ AutomorphicForm.ellipticCell K,
      ∑ᶠ δ₀ ∈ Fam γ₀, eL δ₀ * J δ₀ = Cst * (eK γ₀ * ∑ ξK ∈ Ξ, IK ξK γ₀) := by
    rintro γ₀ ⟨hγ₀R, hγ₀e⟩

    have hRL₁ : ∀ δ₁ ∈ RL, ∀ δ₂ ∈ RL, ∀ (h : GL (Fin 2) L) (u : Lˣ),
        δ₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h) → δ₁ = δ₂ := by
      intro δ₁ hδ₁ δ₂ hδ₂ h u e
      obtain ⟨δ₀, -, huniq⟩ := hRL δ₂ (hRLsub hδ₂)
      have e2 : δ₂ = δ₀ := huniq δ₂ ⟨hδ₂, 1, 1, by simp⟩
      have e1 : δ₁ = δ₀ := huniq δ₁ ⟨hδ₁, h, u, e⟩
      rw [e1, e2]
    have hRL₂ : ∀ (δ : GL (Fin 2) L) (a : Kˣ),
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) →
        ∃ δ₀ ∈ RL, ∃ (h : GL (Fin 2) L) (u : Lˣ),
          δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
            (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h) := by
      intro δ a ha
      obtain ⟨δ₀, ⟨hδ₀R, hex⟩, -⟩ := hRL δ ⟨_, Or.inl (scalar_mul_mem_ellipticCell a hγ₀e), ha⟩
      exact ⟨δ₀, hδ₀R, hex⟩

    have hAex : ∀ δ₀ : GL (Fin 2) L, ∃ A : Kˣ,
        (∃ a : Kˣ, LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) A * γ₀) := by
      intro δ₀
      by_cases h : ∃ a : Kˣ, LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)
      · exact ⟨h.choose, fun _ => h.choose_spec⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose A hA using hAex

    have hvan' : ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
        ¬ LT.TwistedNorm.IsNormClass hgen
            (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
        (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
          AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
            AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
              (AutomorphicForm.centralScalar (𝓞 K) K u)) →
        c₀ ≠ 0 →
        ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K (ιK a * u)} :
            Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
        ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              AutomorphicForm.centralScalar (𝓞 K) K (ιK a * u)) τ f I → I = 0 := by
      intro a u hna hc hc0 τ hτ I hI
      obtain ⟨w, hw, rfl⟩ := hI
      have h0 := hvan γ₀ hγ₀R hγ₀e a u hna hc τ hτ _ ⟨w, hw, rfl⟩
      rw [integral_smul_nnreal_measure] at h0
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h hc0
      · exact h

    set Y : Kˣ → ℂ := fun a => ∑ ξK ∈ Ξ, ∫ u in Set.range Nid,
        ((ξK ⟨ιK a * u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * slabO K γ₀ (ΨK γ₀) f (ιK a * u) ∂νZK with hY
    set Φ : Kˣ → ℂ := fun a => Cst * Y a with hΦ
    have hξ1 : ∀ ξK ∈ Ξ, ∀ s : Kˣ, ξK ⟨ιK s, Subgroup.mem_top _⟩ = 1 :=
      fun ξK hξK s => ((hΞ ξK).1 hξK).2.1 (ιK s) ⟨s, rfl⟩
    have hξmul : ∀ (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (x y : (AdeleRing (𝓞 K) K)ˣ),
        ξK ⟨x * y, Subgroup.mem_top _⟩ = ξK ⟨x, Subgroup.mem_top _⟩ * ξK ⟨y, Subgroup.mem_top _⟩ := by
      intro ξK x y
      rw [← map_mul]
      rfl
    have hΦS : ∀ a s : Kˣ, (∃ h : GL (Fin 2) K,
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * γ₀ = h⁻¹ * γ₀ * h) → Φ (a * s) = Φ a := by
      rintro a s ⟨h, hsh⟩
      show Cst * Y (a * s) = Cst * Y a
      congr 1
      refine Finset.sum_congr rfl fun ξK hξK => ?_
      congr 1
      funext u
      have e1 : ιK (a * s) * u = ιK s * (ιK a * u) := by
        rw [map_mul]; simp only [mul_comm, mul_left_comm]
      have e2 : slabO K γ₀ (ΨK γ₀) f (ιK s * (ιK a * u)) = slabO K γ₀ (ΨK γ₀) f (ιK a * u) :=
        AutomorphicForm.setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
          K α β hα γ₀ (ΨK γ₀) (hΨKs γ₀ hγ₀R) (hΨK γ₀ hγ₀R) f hf hfc (ιK a * u) s h hsh
      rw [e1, e2, hξmul, hξ1 ξK hξK s, one_mul]
    have hΦN : ∀ (a : Kˣ) (b : Lˣ), Φ (a * Units.map (Algebra.norm K : L →* K) b) = Φ a := by
      intro a b
      show Cst * Y (a * Units.map (Algebra.norm K : L →* K) b) = Cst * Y a
      congr 1
      refine Finset.sum_congr rfl fun ξK hξK => ?_
      have hNb : ιK (Units.map (Algebra.norm K : L →* K) b) ∈ Nid.range := by
        refine ⟨Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) b, Units.ext ?_⟩
        simp only [hNid, hιK, M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map, MonoidHom.coe_coe]
        exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap K L b
      have key := setIntegral_range_idelicNorm_mul_norm K L νZK
        (fun v => ((ξK ⟨ιK a * v, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * slabO K γ₀ (ΨK γ₀) f (ιK a * v)) b hNb
      have e1 : ∀ u : (AdeleRing (𝓞 K) K)ˣ, ιK (a * Units.map (Algebra.norm K : L →* K) b) * u =
          ιK a * (ιK (Units.map (Algebra.norm K : L →* K) b) * u) := by
        intro u; rw [map_mul, mul_assoc]
      simp only [e1]
      exact key
    have hΦ0 : ∀ a : Kˣ, ¬ LT.TwistedNorm.IsNormClass hgen
        (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) → Φ a = 0 := by
      intro a hna
      show Cst * Y a = 0
      by_cases hc0 : c₀ = 0
      · rw [hCst, hc0]
        simp
      · have hY0 : Y a = 0 := by
          refine Finset.sum_eq_zero fun ξK hξK => ?_
          refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
          rw [slabO_eq_zero_of_not_isNormClass K L σ.symm hgen α β hα γ₀ hγ₀e (ΨK γ₀) (hΨKs γ₀ hγ₀R)
            (hΨK γ₀ hγ₀R) f hf hfc (fun a' u' hna' hc' => hvan' a' u' hna' hc' hc0) a hna u hu, mul_zero]
        rw [hY0, mul_zero]

    have h5 := LT.TwistedNorm.finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell
      K L σ.symm hgen γ₀ hγ₀e RL hRL₁ hRL₂ A (fun δ₀ _ => hA δ₀) T hT Φ hΦS hΦN hΦ0

    have hJΦ : ∀ δ₀ ∈ Fam γ₀, eL δ₀ * J δ₀ = eL δ₀ * Φ (A δ₀) := by
      rintro δ₀ ⟨hδ₀R, hδ₀⟩
      congr 1
      exact hper δ₀ hδ₀R γ₀ hγ₀R hγ₀e (A δ₀) (hA δ₀ hδ₀)

    have hYsum : ∑ᶠ t ∈ T, Y t = ∑ ξK ∈ Ξ, IK ξK γ₀ :=
      (sum_integral_eq_finsum_sum_setIntegral K L hprime σ.symm hgen νZK ξL Ξ hΞ T hT α β hα γ₀ hγ₀e
        (ΨK γ₀) (hΨKs γ₀ hγ₀R) (hΨK γ₀ hγ₀R) f hf hfc).2
    calc ∑ᶠ δ₀ ∈ Fam γ₀, eL δ₀ * J δ₀
        = ∑ᶠ δ₀ ∈ Fam γ₀, eL δ₀ * Φ (A δ₀) := finsum_mem_congr rfl hJΦ
      _ = ∑ᶠ t ∈ T, eK γ₀ * Φ t := h5
      _ = ∑ᶠ t ∈ T, (eK γ₀ * Cst) * Y t := by
            refine finsum_mem_congr rfl fun t _ => ?_
            show eK γ₀ * (Cst * Y t) = eK γ₀ * Cst * Y t
            rw [mul_assoc]
      _ = (eK γ₀ * Cst) * ∑ᶠ t ∈ T, Y t := (mul_finsum_mem _ _).symm
      _ = Cst * (eK γ₀ * ∑ ξK ∈ Ξ, IK ξK γ₀) := by rw [hYsum]; ring

  have final : ∑ᶠ δ₀ ∈ RL ∩ SL, eL δ₀ * J δ₀ =
      Cst * ∑ ξK ∈ Ξ, ∑ᶠ γ₀ ∈ RK ∩ AutomorphicForm.ellipticCell K, eK γ₀ * IK ξK γ₀ := by
    rw [hpart, finsum_mem_congr rfl hclass, ← mul_finsum_mem]
    congr 1
    rw [← finsum_mem_finset_sum_comm (RK ∩ AutomorphicForm.ellipticCell K) Ξ (fun ξK γ₀ => eK γ₀ * IK ξK γ₀) F2]
    refine finsum_mem_congr rfl fun γ₀ _ => ?_
    rw [Finset.mul_sum]
  exact final

end S_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass
end P2MW
export P2MW.S_AutomorphicForm_finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass (solution)
