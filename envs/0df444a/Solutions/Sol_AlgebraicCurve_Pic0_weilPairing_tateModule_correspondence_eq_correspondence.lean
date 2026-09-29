-- Prove2me | solution 1 for AlgebraicCurve.Pic0.weilPairing_tateModule_correspondence_eq_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c0dd4bc3-0f7a-5f44-a9cf-3773626f9fee

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_weilPairing_tateModule_correspondence_eq_correspondence
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)

    (e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : ∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
        (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
        (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
        (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))

    {F' : Type} [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)

    (C : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F))
    (hC : ∀ (a : TateModule ℓ (Pic0 K F)) (n : ℕ),
        ((C a : TateModule ℓ (Pic0 K F)) : ℕ → Pic0 K F) n =
          Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ ((a : ℕ → Pic0 K F) n))
    (C' : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F))
    (hC' : ∀ (b : TateModule ℓ (Pic0 K F)) (n : ℕ),
        ((C' b : TateModule ℓ (Pic0 K F)) : ℕ → Pic0 K F) n =
          Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ ((b : ℕ → Pic0 K F) n))
    (a b : TateModule ℓ (Pic0 K F)) :
    e (C a) b = e a (C' b) := by
  refine PadicInt.ext_of_toZModPow.mp (fun n => ?_)
  obtain ⟨W⟩ := AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData K F hfg (ℓ ^ n)

  have ha : ((ℓ ^ n : ℕ) : ℤ) • (a : ℕ → Pic0 K F) n = 0 := TateModule.torsion a n
  have hb : ((ℓ ^ n : ℕ) : ℤ) • (b : ℕ → Pic0 K F) n = 0 := TateModule.torsion b n
  have hca : ((ℓ ^ n : ℕ) : ℤ) •
      Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ ((a : ℕ → Pic0 K F) n) = 0 := by
    rw [← hC a n]; exact TateModule.torsion (C a) n
  have hcb : ((ℓ ^ n : ℕ) : ℤ) •
      Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ ((b : ℕ → Pic0 K F) n) = 0 := by
    rw [← hC' b n]; exact TateModule.torsion (C' b) n

  have h3 := AlgebraicCurve.DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence
    φ ψ hφ hψ hFIφ hfinψ hNψ hFIψ hfinφ hNφ W ((a : ℕ → Pic0 K F) n) ((b : ℕ → Pic0 K F) n)
    ha hb hca hcb

  have h1 : W.pair ⟨Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ ((a : ℕ → Pic0 K F) n),
        Pic0.mem_torsion.mpr hca⟩ ⟨(b : ℕ → Pic0 K F) n, Pic0.mem_torsion.mpr hb⟩ =
      ζ n ^ ((e (C a) b).appr n) :=
    he n W (C a) b _ _ (hC a n).symm rfl
  have h2 : W.pair ⟨(a : ℕ → Pic0 K F) n, Pic0.mem_torsion.mpr ha⟩
        ⟨Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ ((b : ℕ → Pic0 K F) n),
          Pic0.mem_torsion.mpr hcb⟩ =
      ζ n ^ ((e a (C' b)).appr n) :=
    he n W a (C' b) _ _ rfl (hC' b n).symm
  have h4 : ζ n ^ ((e (C a) b).appr n) = ζ n ^ ((e a (C' b)).appr n) := by
    rw [← h1, h3, h2]
  have h5 : (e (C a) b).appr n ≡ (e a (C' b)).appr n [MOD ℓ ^ n] := by
    have h6 := ((hζ n).isOfFinOrder (NeZero.ne _)).pow_inj_mod.mp h4
    rwa [← (hζ n).eq_orderOf] at h6
  show PadicInt.toZModPow n (e (C a) b) = PadicInt.toZModPow n (e a (C' b))
  rw [TateModule.toZModPow_eq_appr, TateModule.toZModPow_eq_appr]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h5

end S_AlgebraicCurve_Pic0_weilPairing_tateModule_correspondence_eq_correspondence
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_weilPairing_tateModule_correspondence_eq_correspondence (solution)
