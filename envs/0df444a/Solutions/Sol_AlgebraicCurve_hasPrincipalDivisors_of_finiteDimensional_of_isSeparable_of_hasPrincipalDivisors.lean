-- Prove2me | solution 1 for AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f92a23f1-2af2-5444-8b17-f9b4d37c47f9

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver_of_isSeparable
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.mem_restrict_iff Divisor.pushforward Divisor.degree_pushforward Divisor.pushforward_apply Place.mem_of_eval_monic_eq_zero Place.mem_fiberOver Place.restrict_mem_fiberOver Place.ord_norm_eq_sum_fiberOver_of_isSeparable Place.mem_iff_ord_nonneg Place.ord_nonneg_of_mem"
namespace HPDSepExt
p2m_open "AlgebraicCurve"

open Polynomial
open scoped Classical

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] [HasPrincipalDivisors K F]

def badOf (c : F) : Finset (Place K F) :=
  if hc : c = 0 then ∅ else (HasPrincipalDivisors.exists_divisor (K := K) c hc).choose.support

theorem ord_eq_zero_of_not_mem_badOf {c : F} {v : Place K F} (hv : v ∉ badOf (K := K) c) (hc : c ≠ 0) : v.ord c = 0 := by
  unfold badOf at hv
  rw [dif_neg hc] at hv
  have hD := (HasPrincipalDivisors.exists_divisor (K := K) c hc).choose_spec.1 v
  rw [← hD]
  by_contra h
  exact hv (Finsupp.mem_support_iff.mpr h)

def badPoly (P : Polynomial F) : Finset (Place K F) := P.support.biUnion fun i => badOf (K := K) (P.coeff i)

theorem coeff_mem_of_not_mem_badPoly {P : Polynomial F} {v : Place K F} (hv : v ∉ badPoly (K := K) P) (i : ℕ) :
    P.coeff i ∈ v.toValuationSubring := by
  by_cases hci : P.coeff i = 0
  · rw [hci]; exact zero_mem _
  have hi : i ∈ P.support := Polynomial.mem_support_iff.mpr hci
  have hv' : v ∉ badOf (K := K) (P.coeff i) := by
    intro h; apply hv; unfold badPoly; exact Finset.mem_biUnion.mpr ⟨i, hi, h⟩
  exact (Place.mem_iff_ord_nonneg v hci).mpr (le_of_eq (ord_eq_zero_of_not_mem_badOf hv' hci).symm)

theorem mem_of_aeval_eq_zero {P : Polynomial F} (hP : P.Monic) {x : L} (hx : aeval x P = 0) (w : Place K L)
    (hw : w.restrict F ∉ badPoly (K := K) P) : x ∈ w.toValuationSubring := by
  refine Place.mem_of_eval_monic_eq_zero w (P := P.map (algebraMap F L)) (hP.map _) (fun i => ?_) ?_
  · rw [coeff_map]
    exact (Place.mem_restrict_iff w).mp (coeff_mem_of_not_mem_badPoly hw i)
  · rwa [eval_map, ← aeval_def]

def bad (g : L) : Finset (Place K F) := badPoly (K := K) (minpoly F g) ∪ badPoly (K := K) (minpoly F g⁻¹)

theorem ord_eq_zero_of_restrict_not_mem_bad {g : L} (hg : g ≠ 0) (w : Place K L) (hw : w.restrict F ∉ bad (K := K) (F := F) g) :
    w.ord g = 0 := by
  have hint : IsIntegral F g := IsIntegral.of_finite F g
  have hint' : IsIntegral F g⁻¹ := IsIntegral.of_finite F g⁻¹
  have h1 : g ∈ w.toValuationSubring :=
    mem_of_aeval_eq_zero (minpoly.monic hint) (minpoly.aeval F g) w (fun h => hw (Finset.mem_union_left _ h))
  have h2 : g⁻¹ ∈ w.toValuationSubring :=
    mem_of_aeval_eq_zero (minpoly.monic hint') (minpoly.aeval F g⁻¹) w (fun h => hw (Finset.mem_union_right _ h))
  have e1 := Place.ord_nonneg_of_mem w h1
  have e2 := Place.ord_nonneg_of_mem w h2
  rw [Place.ord_inv] at e2
  omega

def suppOf (g : L) : Finset (Place K L) := (bad (K := K) (F := F) g).biUnion fun v => v.fiberOver L

theorem mem_suppOf_of_ord_ne_zero {g : L} (hg : g ≠ 0) {w : Place K L} (hw : w.ord g ≠ 0) : w ∈ suppOf (K := K) (F := F) g := by
  by_contra h
  apply hw
  apply ord_eq_zero_of_restrict_not_mem_bad (F := F) hg
  intro hb
  apply h
  unfold suppOf
  exact Finset.mem_biUnion.mpr ⟨_, hb, Place.restrict_mem_fiberOver w⟩

def divOf {g : L} (hg : g ≠ 0) : Divisor K L :=
  Finsupp.onFinset (suppOf (K := K) (F := F) g) (fun w => w.ord g) (fun w hw => mem_suppOf_of_ord_ne_zero (F := F) hg hw)

@[scoped simp] theorem divOf_apply {g : L} (hg : g ≠ 0) (w : Place K L) : divOf (K := K) (F := F) hg w = w.ord g := by
  simp [divOf]

theorem pushforward_divOf_apply {g : L} (hg : g ≠ 0) (v : Place K F) :
    Divisor.pushforward F (divOf (K := K) (F := F) hg) v = v.ord (Algebra.norm F g) := by
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver_of_isSeparable v hg]

  rw [← Finset.sum_filter]
  have hsub : (divOf (K := K) (F := F) hg).support.filter (fun w => w.restrict F = v) ⊆ v.fiberOver L := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact (Place.mem_fiberOver v).mpr hw.2
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [divOf_apply, mul_comm]
  · intro w hwf hwn
    have hres : w.restrict F = v := (Place.mem_fiberOver v).mp hwf
    have : w ∉ (divOf (K := K) (F := F) hg).support := fun h => hwn (Finset.mem_filter.mpr ⟨h, hres⟩)
    rw [Finsupp.mem_support_iff, not_not, divOf_apply] at this
    rw [this, mul_zero]

theorem degree_divOf {g : L} (hg : g ≠ 0) : Divisor.degree (divOf (K := K) (F := F) hg) = 0 := by
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (Algebra.norm F g) (Algebra.norm_ne_zero_iff.mpr hg)
  have hpush : Divisor.pushforward F (divOf (K := K) (F := F) hg) = E := by
    ext v; rw [pushforward_divOf_apply, hE]
  rw [← Divisor.degree_pushforward (F := F), hpush, hdeg]

end AlgebraicCurve.HPDSepExt
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.AlgebraicCurve P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.AlgebraicCurve.HPDSepExt"
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.AlgebraicCurve P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.AlgebraicCurve.HPDSepExt"

open AlgebraicCurve.HPDSepExt in

theorem solution
    (K F L : Type*) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L] [HasPrincipalDivisors K F] :
    HasPrincipalDivisors K L  :=
  ⟨fun g hg => ⟨divOf (K := K) (F := F) hg, fun w => divOf_apply hg w, degree_divOf hg⟩⟩

end S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
end P2MW
export P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors (solution)
