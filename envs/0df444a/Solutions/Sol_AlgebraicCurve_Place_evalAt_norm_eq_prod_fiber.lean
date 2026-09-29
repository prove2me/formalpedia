-- Prove2me | solution 1 for AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/041d3a7b-c796-598b-ae2b-5d6f9e6a9f6d

import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_inertiaDeg_fiberCenter
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_Algebra_norm_of_subsingleton
import Theorems.Thm_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
import Theorems.Thm_Algebra_norm_prod
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

noncomputable section

open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.valuationSubringAlgebra Place.ramificationIndex Place HasPrincipalDivisors Place.IsRational Place.exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve"

attribute [local instance 0] Place.valuationSubringAlgebra

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]

namespace Place
p2m_export "AlgebraicCurve.Place" "mem_maximalIdeal_iff_ord_pos center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq ramificationIndex ramificationIndex_pos restrict fiber mem_fiber ext coe_algebraMap ResidueField ord algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ramificationIndex_eq_ramificationIdx_fiberCenter inertiaDeg_eq_inertiaDeg_fiberCenter inertiaDeg_eq_one_of_isRational exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve.Place"

local instance : DecidableEq (Place K F') := Classical.decEq _

variable (v : Place K F)

scoped instance : Module.Free v.toValuationSubring (integralClosureAt F' v) :=
  Module.free_of_finite_type_torsion_free'

abbrev conductorIdeal : Ideal (integralClosureAt F' v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (integralClosureAt F' v))

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [CharZero F] in

theorem conductorIdeal_ne_top : conductorIdeal (F' := F') v ≠ ⊤ := by

  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := v.toValuationSubring) (S := integralClosureAt F' v)
    (IsLocalRing.maximalIdeal v.toValuationSubring)
    (fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from algebraMap_integralClosureAt_injective v (by rw [hx, map_zero])]
      exact zero_mem _)
  intro htop
  exact hQmax.ne_top (top_le_iff.mp (htop ▸ Ideal.map_le_iff_le_comap.mpr hQover.ge))

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [CharZero F] in

theorem conductorIdeal_ne_bot : conductorIdeal (F' := F') v ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπmem : algebraMap v.toValuationSubring (integralClosureAt F' v) π
      ∈ conductorIdeal (F' := F') v :=
    Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [h, Ideal.mem_bot] at hπmem
  exact hπ.ne_zero (algebraMap_integralClosureAt_injective v (by rw [hπmem, map_zero]))

noncomputable scoped instance conductorQuotientAlgebra :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

omit [Algebra K F'] [IsScalarTower K F F'] [CharZero F] in

theorem residue_norm_eq_norm_mk (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.norm v.toValuationSubring c)
      = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by

  have key : algebraMap v.toValuationSubring
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Algebra.norm v.toValuationSubring c)
      = Algebra.norm
          (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by

    have hequiv := Algebra.norm_eq_of_algEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := v.toValuationSubring)
        (integralClosureAt F' v) (IsLocalRing.maximalIdeal v.toValuationSubring))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk] at hequiv

    have hbase : algebraMap v.toValuationSubring
        (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Algebra.norm v.toValuationSubring c)
          = Algebra.norm
              (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
              ((1 : v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
                ⊗ₜ[v.toValuationSubring] c) := by
      rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul,
        LinearMap.det_baseChange]
    exact hbase.trans hequiv
  exact key

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place"

namespace Place
p2m_export "AlgebraicCurve.Place" "mem_maximalIdeal_iff_ord_pos center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq ramificationIndex ramificationIndex_pos restrict fiber mem_fiber ext coe_algebraMap ResidueField ord algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ramificationIndex_eq_ramificationIdx_fiberCenter inertiaDeg_eq_inertiaDeg_fiberCenter inertiaDeg_eq_one_of_isRational exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {v : Place K F} {w : Place K F'}

abbrev fiberCenterPow (hw : w.restrict F = v) : Ideal (integralClosureAt F' v) :=
  (fiberCenter F' v hw).asIdeal
    ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal

omit [CharZero F] in

theorem conductorIdeal_le_fiberCenterPow (hw : w.restrict F = v) :
    conductorIdeal (F' := F') v ≤ fiberCenterPow hw :=
  Ideal.le_pow_ramificationIdx

omit [CharZero F] in

theorem fiberCenterPow_ne_top (hw : w.restrict F = v) : fiberCenterPow hw ≠ ⊤ := by
  have hpos : 0 < (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal := by
    rw [← ramificationIndex_eq_ramificationIdx_fiberCenter _ hw]
    exact w.ramificationIndex_pos
  intro htop
  refine ((fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot).ne_top
    (top_le_iff.mp ?_)
  calc (⊤ : Ideal (integralClosureAt F' v)) = fiberCenterPow hw := htop.symm
    _ ≤ (fiberCenter F' v hw).asIdeal ^ 1 := Ideal.pow_le_pow_right hpos
    _ = (fiberCenter F' v hw).asIdeal := pow_one _

noncomputable scoped instance fiberCenterPowQuotientAlgebra (hw : w.restrict F = v) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberCenterPow hw))

scoped instance (hw : w.restrict F = v) :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := by
  haveI : IsScalarTower v.toValuationSubring
      (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)

omit [CharZero F] in

theorem isNilpotent_mk_sub_algebraMap (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    IsNilpotent (Ideal.Quotient.mk (fiberCenterPow hw) c
      - algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (IsLocalRing.residue v.toValuationSubring r)) := by

  have halg : algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) (IsLocalRing.residue v.toValuationSubring r)
        = Ideal.Quotient.mk (fiberCenterPow hw)
            (algebraMap v.toValuationSubring (integralClosureAt F' v) r) := rfl
  rw [halg, ← map_sub]

  refine ⟨(IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (fiberCenter F' v hw).asIdeal, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hr _

omit [CharZero F] in

theorem norm_mk_fiberCenterPow (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (fiberCenterPow hw) c)
      = IsLocalRing.residue v.toValuationSubring r
          ^ Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
    (isNilpotent_mk_sub_algebraMap hw hr)

omit [CharZero F] in

theorem finrank_fiberCenterPow (hw : w.restrict F = v) (hwrat : w.IsRational)
    (hvrat : v.IsRational) :
    Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
      = w.ramificationIndex F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  have hne : (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal ≠ 0 := by
    rw [← ramificationIndex_eq_ramificationIdx_fiberCenter _ hw]
    exact w.ramificationIndex_pos.ne'

  haveI := fiberCenter_liesOver hw
  have key : Module.finrank
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal
        ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (fiberCenter F' v hw).asIdeal) = w.ramificationIndex F := by
    rw [Ideal.finrank_prime_pow_ramificationIdx _ _ (fiberCenter F' v hw).ne_bot hne,
      ← Ideal.inertiaDeg_algebraMap, ← inertiaDeg_eq_inertiaDeg_fiberCenter _ hw,
      w.inertiaDeg_eq_one_of_isRational hwrat (hw.symm ▸ hvrat), mul_one,
      ← ramificationIndex_eq_ramificationIdx_fiberCenter _ hw]
  exact key

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place"

namespace Place
p2m_export "AlgebraicCurve.Place" "mem_maximalIdeal_iff_ord_pos center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq ramificationIndex ramificationIndex_pos restrict fiber mem_fiber ext coe_algebraMap ResidueField ord algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ramificationIndex_eq_ramificationIdx_fiberCenter inertiaDeg_eq_inertiaDeg_fiberCenter inertiaDeg_eq_one_of_isRational exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F) [HasPrincipalDivisors K F']

local instance : DecidableEq (Place K F') := Classical.decEq _

omit [CharZero F] [HasPrincipalDivisors K F'] in

def fiberIdeal (w : Place K F') : Ideal (integralClosureAt F' v) :=
  if hw : w.restrict F = v then fiberCenterPow hw else ⊤

omit [CharZero F] [HasPrincipalDivisors K F'] in
theorem fiberIdeal_of_mem {w : Place K F'} (hw : w.restrict F = v) :
    fiberIdeal v w = fiberCenterPow hw := dif_pos hw

omit [CharZero F] [HasPrincipalDivisors K F'] in
theorem fiberIdeal_of_notMem {w : Place K F'} (hw : ¬w.restrict F = v) :
    fiberIdeal v w = ⊤ := dif_neg hw

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem conductorIdeal_le_fiberIdeal (w : Place K F') :
    conductorIdeal (F' := F') v ≤ fiberIdeal v w := by
  by_cases hw : w.restrict F = v
  · rw [fiberIdeal_of_mem v hw]
    exact conductorIdeal_le_fiberCenterPow hw
  · rw [fiberIdeal_of_notMem v hw]
    exact le_top

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem isCoprime_fiberIdeal {w w' : Place K F'} (hne : w ≠ w') :
    IsCoprime (fiberIdeal v w) (fiberIdeal v w') := by
  by_cases hw : w.restrict F = v
  · by_cases hw' : w'.restrict F = v
    · rw [fiberIdeal_of_mem v hw, fiberIdeal_of_mem v hw']
      haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
        (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
      haveI : (fiberCenter F' v hw').asIdeal.IsMaximal :=
        (fiberCenter F' v hw').isPrime.isMaximal (fiberCenter F' v hw').ne_bot
      refine IsCoprime.pow (Ideal.isCoprime_of_isMaximal ?_)
      intro heq
      exact hne (eq_of_fiberCenter_eq hw hw' (HeightOneSpectrum.ext heq))
    · rw [fiberIdeal_of_notMem v hw', ← Ideal.one_eq_top]
      exact isCoprime_one_right
  · rw [fiberIdeal_of_notMem v hw, ← Ideal.one_eq_top]
    exact isCoprime_one_left

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem count_normalizedFactors_conductorIdeal {w : Place K F'} (hw : w.restrict F = v) :
    (normalizedFactors (conductorIdeal (F' := F') v)).count (fiberCenter F' v hw).asIdeal
      = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
          (fiberCenter F' v hw).asIdeal := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (conductorIdeal_ne_bot (F' := F') v) inferInstance (fiberCenter F' v hw).ne_bot).symm

omit [CharZero F] in

theorem conductorIdeal_eq_prod_fiber :
    conductorIdeal (F' := F') v = ∏ w ∈ v.fiber F', fiberIdeal v w := by
  classical
  have hbot := conductorIdeal_ne_bot (F' := F') v
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (conductorIdeal v)
    with hS

  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩

  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiber F').attach.image
    (fun w' => (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', mem_fiber.mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiber F'} =>
      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) (v.fiber F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq (mem_fiber.mp w₁.2) (mem_fiber.mp w₂.2)
      (HeightOneSpectrum.ext h))

  calc
    conductorIdeal (F' := F') v = ∏ Q ∈ S.toFinset, Q ^ S.count Q := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hbot]
    _ = ∏ Q ∈ T, Q ^ S.count Q := by
          refine Finset.prod_subset hsub fun Q _ hQ => ?_
          rw [Multiset.count_eq_zero_of_notMem
            (fun h => hQ (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = ∏ w' ∈ (v.fiber F').attach,
          (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal
            ^ S.count (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal := by
          rw [hT, Finset.prod_image hinj]
    _ = ∏ w' ∈ (v.fiber F').attach, fiberIdeal v w'.1 := by
          refine Finset.prod_congr rfl fun w' _ => ?_
          rw [hS, count_normalizedFactors_conductorIdeal v (mem_fiber.mp w'.2),
            fiberIdeal_of_mem v (mem_fiber.mp w'.2)]
    _ = ∏ w ∈ v.fiber F', fiberIdeal v w := Finset.prod_attach (v.fiber F') (fiberIdeal v)

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem prod_fiberIdeal_le_of_subset {s t : Finset (Place K F')} (hst : s ⊆ t) :
    ∏ w ∈ t, fiberIdeal v w ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  rw [← Finset.prod_sdiff hst]
  exact Ideal.mul_le_right

omit [CharZero F] in

theorem conductorIdeal_le_prod_fiberIdeal (s : Finset (Place K F')) :
    conductorIdeal (F' := F') v ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  calc conductorIdeal (F' := F') v
      = ∏ w ∈ v.fiber F', fiberIdeal v w := conductorIdeal_eq_prod_fiber v
    _ = ∏ w ∈ v.fiber F' ∪ s, fiberIdeal v w := by
        refine Finset.prod_subset Finset.subset_union_left fun w _ hw' => ?_
        exact (fiberIdeal_of_notMem v fun hmem => hw' (mem_fiber.mpr hmem)).trans
          Ideal.one_eq_top.symm
    _ ≤ ∏ w ∈ s, fiberIdeal v w :=
        prod_fiberIdeal_le_of_subset v Finset.subset_union_right

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place"

namespace Place
p2m_export "AlgebraicCurve.Place" "mem_maximalIdeal_iff_ord_pos center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq ramificationIndex ramificationIndex_pos restrict fiber mem_fiber ext coe_algebraMap ResidueField ord algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ramificationIndex_eq_ramificationIdx_fiberCenter inertiaDeg_eq_inertiaDeg_fiberCenter inertiaDeg_eq_one_of_isRational exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F) [HasPrincipalDivisors K F']

local instance : DecidableEq (Place K F') := Classical.decEq _

noncomputable scoped instance fiberIdealQuotientAlgebra (w : Place K F') :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberIdeal v w))

noncomputable scoped instance prodFiberIdealQuotientAlgebra (s : Finset (Place K F')) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_prod_fiberIdeal v s))

omit [Algebra K F'] [IsScalarTower K F F'] [CharZero F] [HasPrincipalDivisors K F'] in

theorem finite_quotient_of_conductorLE (Q : Ideal (integralClosureAt F' v))
    [Algebra (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)]
    [IsScalarTower v.toValuationSubring (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q)] :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q) :=
  Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)

set_option maxHeartbeats 4000000 in
omit [CharZero F] in

theorem norm_mk_prod_fiberIdeal (c : integralClosureAt F' v) (s : Finset (Place K F')) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c)
      = ∏ w ∈ s,
          Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>

      haveI : Subsingleton
          (integralClosureAt F' v ⧸ (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [Finset.prod_empty]; exact Ideal.one_eq_top)
      conv_rhs => rw [Finset.prod_empty]
      exact Algebra.norm_of_subsingleton _
  | cons a s ha ih =>

      have hcop : IsCoprime (fiberIdeal v a) (∏ w ∈ s, fiberIdeal v w) :=
        IsCoprime.prod_right fun w hw => isCoprime_fiberIdeal v (fun h => ha (h ▸ hw))
      have hprod : ∏ w ∈ Finset.cons a s ha, fiberIdeal v w
          = fiberIdeal v a ⊓ ∏ w ∈ s, fiberIdeal v w := by
        rw [Finset.prod_cons, Ideal.mul_eq_inf_of_isCoprime hcop]

      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        IsScalarTower.of_algebraMap_eq' rfl
      haveI := finite_quotient_of_conductorLE v (fiberIdeal v a)
      haveI := finite_quotient_of_conductorLE v (∏ w ∈ s, fiberIdeal v w)

      set e : (integralClosureAt F' v ⧸ (∏ w ∈ Finset.cons a s ha, fiberIdeal v w)) ≃+*
          (integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        (Ideal.quotEquivOfEq hprod).trans
          (Ideal.quotientInfEquivQuotientProd _ _ hcop) with he

      have hemk : ∀ x : integralClosureAt F' v,
          e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
        intro x
        rw [he, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
        exact Prod.ext
          (by rw [Ideal.quotientInfEquivQuotientProd_fst, Ideal.Quotient.factor_mk])
          (by rw [Ideal.quotientInfEquivQuotientProd_snd, Ideal.Quotient.factor_mk])

      have hkey : Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)
            = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
                ((Ideal.Quotient.mk (fiberIdeal v a) c,
                  Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) :
                  (integralClosureAt F' v ⧸ fiberIdeal v a)
                    × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)) := by
        refine (Algebra.norm_eq_of_equiv_equiv
          (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring)) e ?_
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)).trans ?_
        ·
          refine RingHom.ext fun x => ?_
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
          exact (hemk (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm
        ·
          rw [hemk]
          rfl
      calc (Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c))
          = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (fiberIdeal v a) c)
            * Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) := by
            rw [hkey]; exact Algebra.norm_prod _
        _ = ∏ w ∈ Finset.cons a s ha,
              Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
                (Ideal.Quotient.mk (fiberIdeal v w) c) := by
            rw [Finset.prod_cons, ih]

omit [CharZero F] in

theorem norm_mk_conductor_eq_prod_fiber (c : integralClosureAt F' v) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
      = ∏ w ∈ v.fiber F',
          Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  rw [← norm_mk_prod_fiberIdeal v c (v.fiber F')]

  have he : (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
        = Ideal.Quotient.mk (∏ w ∈ v.fiber F', fiberIdeal v w) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (conductorIdeal_eq_prod_fiber (F' := F') v)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place"

namespace Place
p2m_export "AlgebraicCurve.Place" "mem_maximalIdeal_iff_ord_pos center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq ramificationIndex ramificationIndex_pos restrict fiber mem_fiber ext coe_algebraMap ResidueField ord algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ramificationIndex_eq_ramificationIdx_fiberCenter inertiaDeg_eq_inertiaDeg_fiberCenter inertiaDeg_eq_one_of_isRational exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {v : Place K F} [HasPrincipalDivisors K F']

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem sub_algebraMap_evalAt_mem_fiberCenter {w : Place K F'} (hw : w.restrict F = v)
    (hwrat : w.IsRational) {c : integralClosureAt F' v}
    (_hc : algebraMap (integralClosureAt F' v) F' c ≠ 0)
    (_hord : w.ord (algebraMap (integralClosureAt F' v) F' c) = 0) :
    c - algebraMap v.toValuationSubring (integralClosureAt F' v)
        (algebraMap K v.toValuationSubring
          (w.evalAt (algebraMap (integralClosureAt F' v) F' c)))
      ∈ (fiberCenter F' v hw).asIdeal := by
  set lam : K := w.evalAt (algebraMap (integralClosureAt F' v) F' c) with hlam
  set d : integralClosureAt F' v := c - algebraMap v.toValuationSubring
    (integralClosureAt F' v) (algebraMap K v.toValuationSubring lam) with hd

  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]; exact Ideal.zero_mem _
  rw [mem_fiberCenter_iff_ord_pos hw hd0]

  have hcoe : algebraMap (integralClosureAt F' v) F' d
      = algebraMap (integralClosureAt F' v) F' c - algebraMap K F' lam := by
    rw [hd, map_sub]
    congr 1
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply v.toValuationSubring
      F F',
      show (algebraMap v.toValuationSubring F) (algebraMap K v.toValuationSubring lam)
        = algebraMap K F lam from v.coe_algebraMap lam,
      ← IsScalarTower.algebraMap_apply]

  have hmem : algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring :=
    forall_mem_of_restrict_eq hw c
  have hres : residue w.toValuationSubring ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
      = algebraMap K w.ResidueField lam := (w.algebraMap_evalAt hwrat hmem).symm

  have hdmem : algebraMap (integralClosureAt F' v) F' d ∈ w.toValuationSubring := by
    rw [hcoe]
    exact sub_mem hmem (w.algebraMap_mem' lam)
  have hdF : algebraMap (integralClosureAt F' v) F' d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hd0
  rw [← w.mem_maximalIdeal_iff_ord_pos hdF hdmem]
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨algebraMap (integralClosureAt F' v) F' d, hdmem⟩ : w.toValuationSubring)
      = ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
        - algebraMap K w.toValuationSubring lam := by
    refine Subtype.ext ?_
    show algebraMap (integralClosureAt F' v) F' d
      = ((⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
          - algebraMap K w.toValuationSubring lam : w.toValuationSubring) : F')
    rw [hcoe]
    push_cast
    rw [w.coe_algebraMap]
  rw [hsplit, map_sub, hres, sub_eq_zero, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place"

namespace Place
p2m_export "AlgebraicCurve.Place" "mem_maximalIdeal_iff_ord_pos center valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq ramificationIndex ramificationIndex_pos restrict fiber mem_fiber ext coe_algebraMap ResidueField ord algebraMap_mem' toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt ramificationIndex_eq_ramificationIdx_fiberCenter inertiaDeg_eq_inertiaDeg_fiberCenter inertiaDeg_eq_one_of_isRational exists_integralClosureAt_of_ord_fiber_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {v : Place K F} [HasPrincipalDivisors K F']

local instance : DecidableEq (Place K F') := Classical.decEq _

omit [CharZero F] in

theorem algebraMap_evalAt_coe (hv : v.IsRational) (r : v.toValuationSubring) :
    algebraMap K v.ResidueField
        (v.evalAt (algebraMap v.toValuationSubring F r))
      = IsLocalRing.residue v.toValuationSubring r := by
  have hcoe : algebraMap v.toValuationSubring F r = (r : F) := rfl
  rw [hcoe]
  have hmem : (r : F) ∈ v.toValuationSubring := r.2
  rw [v.algebraMap_evalAt hv hmem]

omit [CharZero F] in

theorem residue_algebraMap (lam : K) :
    IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring lam)
      = algebraMap K v.ResidueField lam := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem norm_mk_fiberIdeal_eq_norm_mk_fiberCenterPow {w : Place K F'}
    (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (fiberIdeal v w) c)
      = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (fiberCenterPow hw) c) := by
  have he : (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw))
      (Ideal.Quotient.mk (fiberIdeal v w) c) = Ideal.Quotient.mk (fiberCenterPow hw) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (fiberIdeal_of_mem v hw)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

omit [CharZero F] in

theorem residue_norm_eq_prod_evalAt (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) {c : integralClosureAt F' v}
    (hc : algebraMap (integralClosureAt F' v) F' c ≠ 0)
    (hord : ∀ w ∈ v.fiber F', w.ord (algebraMap (integralClosureAt F' v) F' c) = 0) :
    IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c)
      = ∏ w ∈ v.fiber F',
          algebraMap K v.ResidueField
              (w.evalAt (algebraMap (integralClosureAt F' v) F' c))
            ^ w.ramificationIndex F := by
  classical

  rw [residue_norm_eq_norm_mk v c, norm_mk_conductor_eq_prod_fiber v c]

  refine Finset.prod_congr rfl fun w hw => ?_
  have hwv : w.restrict F = v := mem_fiber.mp hw

  have hsub := sub_algebraMap_evalAt_mem_fiberCenter hwv (hrat w hw) hc (hord w hw)

  rw [norm_mk_fiberIdeal_eq_norm_mk_fiberCenterPow hwv c, norm_mk_fiberCenterPow hwv hsub,
    finrank_fiberCenterPow hwv (hrat w hw) hv, residue_algebraMap]

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve"

open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.AlgebraicCurve.Place in
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F) (f : F') (hf : f ≠ 0) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) : v.evalAt (Algebra.norm F f) = ∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F) := by
  classical

  obtain ⟨c, rfl⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg
    (v := v) hf (fun w hw => (hord w hw).ge)
  have hc : c ≠ 0 := fun h => hf (by rw [h, map_zero])

  have hnorm : Algebra.norm F (algebraMap (integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c) := by
    rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v), Algebra.intNorm_eq_norm]

  refine v.algebraMap_residueField_injective ?_
  rw [hnorm]

  have hlhs : algebraMap K v.ResidueField
      (v.evalAt (algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c)))
        = IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c) :=
    Place.algebraMap_evalAt_coe hv _
  rw [hlhs, Place.residue_norm_eq_prod_evalAt hv hrat hf hord, map_prod]

  exact Finset.prod_congr rfl fun w hw => (map_pow _ _ _).symm

end
end S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber
end P2MW
export P2MW.S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber (solution)
