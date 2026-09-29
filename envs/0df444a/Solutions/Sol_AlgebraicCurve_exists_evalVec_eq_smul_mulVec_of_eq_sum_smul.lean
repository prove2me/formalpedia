-- Prove2me | solution 1 for AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e4fd87d0-7a7b-57ec-84ef-cd3aeeaa91c3

import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "pivotIndex evalVec Place"
p2m_open "AlgebraicCurve"

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_mul ord_inv exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one mem_of_ord_nonneg" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_algebraMap'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_add'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_smul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul' hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap']

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_smul'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_sum_smul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {ι : Type*} (S : Finset ι) (a : ι → K) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    (∑ i ∈ S, a i • f i) ∈ v.toValuationSubring ∧
      v.evalAt (∑ i ∈ S, a i • f i) = ∑ i ∈ S, a i * v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero (algebraMap K F), v.evalAt_algebraMap']
  | @insert i S hi ih =>
    obtain ⟨hmem, heq⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    have hsm : a i • f i ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]
      exact mul_mem (v.algebraMap_mem' _) hfi
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_insert hi]
      exact add_mem hsm hmem
    · rw [Finset.sum_insert hi, Finset.sum_insert hi, v.evalAt_add' hv hsm hmem, heq,
        v.evalAt_smul' hv (a i) hfi]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_sum_smul'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.isUnit_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hf⟩ : v.toValuationSubring) = u := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_ne_zero_of_inv_mem' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hfi : f⁻¹ ∈ v.toValuationSubring) (hf0 : f ≠ 0) : v.evalAt f ≠ 0 := by
  intro h0
  have h1 : v.evalAt (f * f⁻¹) = 1 := by rw [mul_inv_cancel₀ hf0, v.evalAt_one]
  rw [v.evalAt_mul' hv hf hfi, h0, zero_mul] at h1
  exact zero_ne_one h1

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_ne_zero_of_inv_mem'"
end AlgebraicCurve

theorem solution
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (hr : 0 < r)
    (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ i, t i ≠ 0)
    (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (hM : Minv * M = 1) (hM' : M * Minv = 1)
    (hst : ∀ i, s i = ∑ j, M i j • t j)
    (P : Place (AlgebraicClosure ℚ) F) (hP : P.IsRational)
    (c : Fin r) (hc : ∀ j, t j * (t c)⁻¹ ∈ P.toValuationSubring) :
    ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      evalVec s P = d • M.mulVec (fun j => P.evalAt (t j * (t c)⁻¹)) := by
  classical
  set k := pivotIndex s P hr with hk

  have hkmin : ∀ j, P.ord (s k) ≤ P.ord (s j) := by
    have hex : ∃ i : Fin r, ∀ j : Fin r, P.ord (s i) ≤ P.ord (s j) := by
      obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => P.ord (s i)) ⟨c, Finset.mem_univ _⟩
      exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
    have : k = Classical.choose hex := by
      rw [hk, pivotIndex, dif_pos hex]
    rw [this]
    exact Classical.choose_spec hex

  have hts : ∀ l, t l = ∑ j, Minv l j • s j := by
    intro l
    simp_rw [hst, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ x, (∑ j, (Minv l j * M j x)) • t x = (Minv * M) l x • t x := by
      intro x
      rw [Matrix.mul_apply]
    simp_rw [← Finset.sum_smul, this, hM, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

  have hsc : ∀ i, s i * (t c)⁻¹ ∈ P.toValuationSubring ∧
      P.evalAt (s i * (t c)⁻¹) = ∑ j, M i j * P.evalAt (t j * (t c)⁻¹) := by
    intro i
    have hsum : s i * (t c)⁻¹ = ∑ j, M i j • (t j * (t c)⁻¹) := by
      rw [hst i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc]
    rw [hsum]
    exact P.evalAt_sum_smul' hP Finset.univ (fun j => M i j) (fun j => t j * (t c)⁻¹) (fun j _ => hc j)

  have hjk : ∀ j, s j * (s k)⁻¹ ∈ P.toValuationSubring := by
    intro j
    refine P.mem_of_ord_nonneg (mul_ne_zero (hs0 j) (inv_ne_zero (hs0 k))) ?_
    rw [P.ord_mul (hs0 j) (inv_ne_zero (hs0 k)), P.ord_inv]
    have := hkmin j
    omega
  have htk : t c * (s k)⁻¹ ∈ P.toValuationSubring := by
    have hsum : t c * (s k)⁻¹ = ∑ j, Minv c j • (s j * (s k)⁻¹) := by
      rw [hts c, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc]
    rw [hsum]
    exact (P.evalAt_sum_smul' hP Finset.univ (fun j => Minv c j) (fun j => s j * (s k)⁻¹) (fun j _ => hjk j)).1
  have hkt : s k * (t c)⁻¹ ∈ P.toValuationSubring := (hsc k).1
  have hinv : (t c * (s k)⁻¹)⁻¹ = s k * (t c)⁻¹ := by
    rw [mul_inv, inv_inv, mul_comm]
  set d : AlgebraicClosure ℚ := P.evalAt (t c * (s k)⁻¹) with hd
  have hd0 : d ≠ 0 := P.evalAt_ne_zero_of_inv_mem' hP htk (hinv ▸ hkt)
    (mul_ne_zero (ht0 c) (inv_ne_zero (hs0 k)))
  refine ⟨d, hd0, ?_⟩
  funext i
  have hfac : s i * (s k)⁻¹ = (s i * (t c)⁻¹) * (t c * (s k)⁻¹) := by
    field_simp [ht0 c, hs0 k]
  simp only [evalVec, dif_pos hr, ← hk, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [hfac, P.evalAt_mul' hP (hsc i).1 htk, (hsc i).2, ← hd, mul_comm]

end S_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
end P2MW
export P2MW.S_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul (solution)
