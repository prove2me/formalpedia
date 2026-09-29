-- Prove2me | solution 1 for AlgebraicCurve.Divisor.ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ecf2f349-b6bb-5c55-8bdc-75d7f310ed31

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_congr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence Divisor.correspondence_apply Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pullbackAlong_apply Place Divisor HasPrincipalDivisors Place.smul_toValuationSubring Place.ord_smul Divisor.smul_single Divisor.smul_apply SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.smul_single Divisor.pullbackAlong_pullbackAlong Divisor.pushforwardAlong_pushforwardAlong Divisor.pushforwardAlong_pullbackAlong_of_surjective"
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong ext ord ord_coe_irreducible smul_toValuationSubring ord_smul toValuationSubring"
p2m_open "AlgebraicCurve.Place"

theorem l1_mem_restrictAlong_iff [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem l1_isIntegral_algEquiv (u : F ≃ₐ[K] F) : (u : F →ₐ[K] F).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ u.surjective

theorem l1_restrictAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F)
    (hu : (u : F →ₐ[K] F).toRingHom.IsIntegral) (w : Place K F) :
    w.restrictAlong (u : F →ₐ[K] F) hu = u⁻¹ • w := by
  ext f
  rw [l1_mem_restrictAlong_iff, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
  rfl

theorem l1_ramificationIndexAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F) (w : Place K F) :
    Place.ramificationIndexAlong (u : F →ₐ[K] F) w = 1 := by
  have hu := l1_isIntegral_algEquiv (K := K) u
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (u⁻¹ • w).toValuationSubring
  have h1 : (u⁻¹ • w).ord (π : F) = 1 := (u⁻¹ • w).ord_coe_irreducible hπ
  have h2 : w.ord (u (π : F)) = 1 := by
    have := Place.ord_smul u (u⁻¹ • w) (π : F)
    rwa [smul_inv_smul, h1] at this
  have h3 := Place.ord_restrictAlong (u : F →ₐ[K] F) hu w (π : F)
  rw [l1_restrictAlong_algEquiv u hu w, h1, mul_one, AlgEquiv.coe_algHom, h2] at h3
  exact_mod_cast h3.symm

end Place

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "pullbackAlong pushforwardAlong correspondence correspondence_apply pullbackAlong_apply smul_def smul_single smul_apply pullbackAlong_pullbackAlong pushforwardAlong_pushforwardAlong pushforwardAlong_pullbackAlong_of_surjective"
p2m_open "AlgebraicCurve.Divisor"

theorem l1_pullbackAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F)
    (hu : (u : F →ₐ[K] F).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong (u : F →ₐ[K] F) hu D = u • D := by
  ext w
  rw [Divisor.pullbackAlong_apply, Place.l1_ramificationIndexAlong_algEquiv, Place.l1_restrictAlong_algEquiv,
    Divisor.smul_apply, Nat.cast_one, one_mul]

theorem l1_pushforwardAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F)
    (hu : (u : F →ₐ[K] F).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pushforwardAlong (u : F →ₐ[K] F) hu D = u⁻¹ • D := by
  have h := Divisor.pushforwardAlong_pullbackAlong_of_surjective (u : F →ₐ[K] F) hu u.surjective (u⁻¹ • D)
  rwa [l1_pullbackAlong_algEquiv, smul_inv_smul] at h

theorem l1_pullbackAlong_congr [HasPrincipalDivisors K F'] {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong φ' hφ' D := by
  subst h; rfl

theorem l1_pushforwardAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong φ' hφ' D := by
  subst h; rfl

theorem smul_correspondence_eq_correspondence_smul_of_comp_eq_comp
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (g : F' ≃ₐ[K] F') (s t : F ≃ₐ[K] F)
    (h1 : (g : F' →ₐ[K] F').comp ψ = φ.comp (s : F →ₐ[K] F))
    (h2 : (g : F' →ₐ[K] F').comp φ = ψ.comp (t : F →ₐ[K] F))
    (D : Divisor K F) :
    s • Divisor.correspondence φ ψ hφ hψ D = Divisor.correspondence ψ φ hψ hφ (t • D) := by
  have hg := Place.l1_isIntegral_algEquiv (K := K) g
  have hs := Place.l1_isIntegral_algEquiv (K := K) s
  have ht := Place.l1_isIntegral_algEquiv (K := K) t
  have hgψ : ((g : F' →ₐ[K] F').comp ψ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hψ hg
  have hgφ : ((g : F' →ₐ[K] F').comp φ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hφ hg
  have hφs : (φ.comp (s : F →ₐ[K] F)).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hs hφ
  have hψt : (ψ.comp (t : F →ₐ[K] F)).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ ht hψ

  have hpull : Divisor.pullbackAlong ψ hψ (t • D) = g • Divisor.pullbackAlong φ hφ D := by
    rw [← l1_pullbackAlong_algEquiv t ht D, Divisor.pullbackAlong_pullbackAlong (t : F →ₐ[K] F) ψ ht hψ hψt,
      ← l1_pullbackAlong_congr h2 hgφ hψt, ← Divisor.pullbackAlong_pullbackAlong φ (g : F' →ₐ[K] F') hφ hg hgφ,
      l1_pullbackAlong_algEquiv]

  have hpush : ∀ E : Divisor K F', Divisor.pushforwardAlong ψ hψ (g⁻¹ • E) = s⁻¹ • Divisor.pushforwardAlong φ hφ E := by
    intro E
    rw [← l1_pushforwardAlong_algEquiv g hg E, Divisor.pushforwardAlong_pushforwardAlong ψ (g : F' →ₐ[K] F') hψ hg hgψ,
      l1_pushforwardAlong_congr h1 hgψ hφs, ← Divisor.pushforwardAlong_pushforwardAlong (s : F →ₐ[K] F) φ hs hφ hφs,
      l1_pushforwardAlong_algEquiv]
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, hpull]
  have := hpush (g • Divisor.pullbackAlong φ hφ D)
  rw [inv_smul_smul] at this
  rw [this, smul_inv_smul]

end Divisor

end AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (g : F' ≃ₐ[K] F') (s t : F ≃ₐ[K] F)
    (h1 : (g : F' →ₐ[K] F').comp ψ = φ.comp (s : F →ₐ[K] F))
    (h2 : (g : F' →ₐ[K] F').comp φ = ψ.comp (t : F →ₐ[K] F))
    (D : Divisor K F) :
    SemilinearAut.ofAlgAut s • Divisor.correspondence φ ψ hφ hψ D =
      Divisor.correspondence ψ φ hψ hφ (SemilinearAut.ofAlgAut t • D) := by
  have key : ∀ (u : F ≃ₐ[K] F) (E : Divisor K F), SemilinearAut.ofAlgAut u • E = u • E := by
    intro u E
    induction E using Finsupp.induction with
    | zero => rw [smul_zero, smul_zero]
    | single_add v n E _ _ ih =>
      rw [smul_add, smul_add, ih, AlgebraicCurve.Divisor.smul_single, AlgebraicCurve.SemilinearAut.smul_single]
      congr 2
  rw [key, key]
  exact AlgebraicCurve.Divisor.smul_correspondence_eq_correspondence_smul_of_comp_eq_comp φ ψ hφ hψ g s t h1 h2 D

end S_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp (solution)
