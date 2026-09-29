-- Prove2me | solution 1 for AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3ce045b2-35a1-56d8-8e9a-8aef23d6c979

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false

noncomputable section

open KaehlerDifferential IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place HasCanonicalDivisor polarDifferentials HasCanonicalLocalResidueKStar kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK_apply ResidueTheoremK HasCanonicalLocalResidueKStar.dataKStar diagonalHom adeleSpace diagonal_mem_adeleSpace residueTheoremK_of_isAlgClosed dCoordGenerates_of_isCurveOver IsCurveOver.exists_separating_transcendental isCurveOver_ratFunc"
p2m_open "AlgebraicCurve"

namespace ResThm

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem residueTheoremK : ResidueTheoremK K F := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨t, ht, hfin, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfin
  haveI := hsep

  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F := ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    ext y
    show algebraMap K⟮t⟯ F (e (e.symm y)) = algebraMap K⟮t⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  exact residueTheoremK_of_isAlgClosed (K := K) (F := F)

variable {K F}

theorem trace_res_differentialCoeff_of_hasSimpleResidue {v : Place K F} {ω : Ω[F⁄K]} {a : K}
    (h : v.HasSimpleResidue ω a) :
    Algebra.trace K v.ResidueField
        ((HasCanonicalLocalResidueKStar.dataKStar v).res (v.differentialCoeff ω)) = a := by
  obtain ⟨f, hf, hval⟩ := h
  have hdeg : Module.finrank K v.ResidueField = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed v
  rw [v.differentialCoeff_unique hf, (HasCanonicalLocalResidueKStar.dataKStar v).res_simplePole f hval.mem,
    hval.residue_eq, Algebra.trace_algebraMap, hdeg, one_smul]

theorem res_differentialCoeff_eq_zero_of_isRegularAt {v : Place K F} {ω : Ω[F⁄K]}
    (h : v.IsRegularAt ω) :
    (HasCanonicalLocalResidueKStar.dataKStar v).res (v.differentialCoeff ω) = 0 := by
  obtain ⟨f, hf, hωf⟩ := h
  rw [v.differentialCoeff_unique hωf]
  exact (HasCanonicalLocalResidueKStar.dataKStar v).res_of_mem f hf

theorem eq_zero_of_hasSimpleResidue_zero {v : Place K F} {a : K} (h : v.HasSimpleResidue (0 : Ω[F⁄K]) a) :
    a = 0 := by
  have ht := trace_res_differentialCoeff_of_hasSimpleResidue h
  rw [v.differentialCoeff_zero, map_zero, map_zero] at ht
  exact ht.symm

theorem main (S : Finset (Place K F)) (ω : Ω[F⁄K])
    (hω : ω ∈ polarDifferentials K F (S : Set (Place K F)))
    (a : Place K F → K) (ha : ∀ v ∈ S, v.HasSimpleResidue ω (a v)) :
    ∑ v ∈ S, a v = 0 := by
  classical
  rcases eq_or_ne ω 0 with rfl | hω0
  · exact Finset.sum_eq_zero fun v hv => eq_zero_of_hasSimpleResidue_zero (ha v hv)
  · have hRT := residueTheoremK K F
    have h := hRT HasCanonicalLocalResidueKStar.dataKStar hω0 1
    rw [weilOfKaehlerK_apply] at h

    have hterm : ∀ v : Place K F,
        kaehlerResidueTermKFam HasCanonicalLocalResidueKStar.dataKStar ω
          ((⟨diagonalHom K F 1, diagonal_mem_adeleSpace 1⟩ : adeleSpace K F) : Place K F → F) v =
        if v ∈ S then a v else 0 := by
      intro v
      rw [kaehlerResidueTermKFam_apply]
      rw [show ((⟨diagonalHom K F 1, diagonal_mem_adeleSpace 1⟩ : adeleSpace K F) : Place K F → F) v = 1
        from rfl, one_mul]
      split_ifs with hv
      · exact trace_res_differentialCoeff_of_hasSimpleResidue (ha v hv)
      · rw [res_differentialCoeff_eq_zero_of_isRegularAt ((hω v).1 (by exact_mod_cast hv)), map_zero]
    rw [finsum_congr hterm] at h
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?_] at h
    · rw [← h]
      exact Finset.sum_congr rfl fun v hv => by rw [if_pos hv]
    · intro v hv
      rw [Function.mem_support] at hv
      by_contra hvS
      exact hv (if_neg (by exact_mod_cast hvS))

end ResThm

end AlgebraicCurve

end

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (ω : Ω[F⁄K])
    (hω : ω ∈ AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F)))
    (a : AlgebraicCurve.Place K F → K) (ha : ∀ v ∈ S, v.HasSimpleResidue ω (a v)) :
    ∑ v ∈ S, a v = 0 := by
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : ∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  exact AlgebraicCurve.ResThm.main S ω hω a ha

#print axioms solution

end S_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
end P2MW
export P2MW.S_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials (solution)
