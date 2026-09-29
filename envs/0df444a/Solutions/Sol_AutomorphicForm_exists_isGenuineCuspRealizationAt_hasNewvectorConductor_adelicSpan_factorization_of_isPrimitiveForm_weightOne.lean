-- Prove2me | solution 1 for AutomorphicForm.exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c8a3d980-1b43-5b2f-aed3-8e30483e44ce

import Theorems.Thm_DihedralWeightOne_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm
import Theorems.Thm_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckeIntegralSeam.finite_padicInt_quotient_span_p Deep.NTSupply.instNormalRayClassSubgroup LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

open CongruenceSubgroup DihedralWeightOne
open scoped MatrixGroups ModularForm

namespace Ws1
namespace CondC2

theorem exists_heightOneSpectrum_mem (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map Rat.ringOfIntegersEquiv.toRingHom
    rw [map_natCast, Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hp.one_lt.ne' h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hp0 : (p : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hp0 hle
  exact ⟨⟨M, hM.isPrime, hMne⟩, hle (Ideal.subset_span rfl)⟩

theorem absNorm_asIdeal_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p := by
  have hdvd : Ideal.absNorm v.asIdeal ∣ p := by
    have h1 : Ideal.span {(p : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hv
    have h2 := Ideal.absNorm_dvd_absNorm_of_le h1
    have h3 : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
      rw [Ideal.absNorm_span_singleton]
      have : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
      rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]
    rwa [h3] at h2
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have key : ∀ n : ℕ, (n : 𝓞 ℚ) ∈ v.asIdeal → n ≠ 1 → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn h1 h0
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨k, rfl⟩ := hpn
      have hk0 : k ≠ 0 := by rintro rfl; exact h0 (by simp)
      rw [Nat.cast_mul] at hn
      rcases v.isPrime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · by_cases hk1 : k = 1
        · subst hk1
          exact absurd (v.asIdeal.eq_top_of_isUnit_mem (by simpa using h) isUnit_one) v.isPrime.ne_top
        · exact ih k (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) hp.one_lt) h hk1 hk0
  refine key (Ideal.absNorm v.asIdeal) (Ideal.absNorm_mem v.asIdeal) ?_ ?_
  · rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

end Ws1.CondC2

open Ws1.CondC2 in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f)
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
        ModularFormClass.qCoeff f p = Θ.a v ∧ ψ (p : ZMod N) = Θ.b v) :
    ∃ (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
      (R' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ'.toRawCentral),
      IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ'.toRawCentral R' ∧
      ∀ (q : ℕ) (_ : Fact q.Prime),
        LocalNewvector.HasNewvectorConductor q (LocalNewvector.AdelicSpan R'.toFun) (N.factorization q) := by
  classical

  obtain ⟨Φ, R, hRf, hRg, hRb, S₁, hpk⟩ :=
    DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm N ψ f hf

  obtain ⟨R', hR'⟩ :=
    AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
      c u d₁ d₂ T hc hd₁ hd hcov Φ.toRawCentral R hRg hRb
  obtain ⟨S₂, hΘ⟩ := hΘ

  have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal ∈ S₁ ∪ S₂ ∪ N.primeFactors} := by
    have hsub : {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal ∈ S₁ ∪ S₂ ∪ N.primeFactors} ⊆
        ⋃ n ∈ (↑(S₁ ∪ S₂ ∪ N.primeFactors) : Set ℕ), {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal = n} := by
      intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨_, hv, rfl⟩
    refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => ?_) hsub
    have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal)
        {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal = n} := fun v _ w _ h => HeightOneSpectrum.ext h
    refine Set.Finite.of_finite_image ?_ hinj
    refine (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ℚ) n).subset ?_
    rintro I ⟨v, hv, rfl⟩
    exact hv
  have hagree : Φ.AgreesAwayFromFinite Θ := by
    refine ⟨hfin.toFinset, fun v hv => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
    have hnorm : Ideal.absNorm v.asIdeal = p := absNorm_asIdeal_eq hp v hpv
    rw [hnorm] at hv
    have hp1 : p ∉ S₁ := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hp2 : p ∉ S₂ := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hpN : ¬ p ∣ N := fun h => hv (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, h, NeZero.ne N⟩))
    obtain ⟨h1, h2⟩ := hpk p hp hp1 hpN v hpv
    obtain ⟨h3, h4⟩ := hΘ p hp hp2 hpN v hpv
    exact ⟨h1.trans h3, h2.trans h4⟩
  refine ⟨Φ, hagree, R', ?_, fun q hq => ?_⟩
  · change Continuous R'.toFun
    rw [hR']
    exact hRg
  · rw [hR', hRf]
    exact DihedralWeightOne.hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm N ψ f hf q

end S_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
end P2MW
export P2MW.S_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne (solution)
