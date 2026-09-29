-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/33518ba7-d0d5-516f-9acd-8ea7fdef887d

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable.AlgebraicCurve IntermediateField"

set_option Elab.async false

set_option autoImplicit false
open IsLocalRing
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Place.ord_neg"
p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation_coe_eq_one_iff ord ord_zero ord_mul ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring ramificationIndex ramificationIndex_pos restrict ord_restrict inertiaDeg IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt ord_neg fiberOver mem_fiberOver restrict_mem_fiberOver ord_eq_zero_iff_adicValuation_eq_one ord_nonneg_of_mem exists_ord_eq_one ord_norm_eq_sum_fiberOver_of_isSeparable inertiaDeg_pos ord_algebraMap"
p2m_open "AlgebraicCurve.Place~mem_of_ord_nonneg"
variable (v : Place K F)

private theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem _root_.AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit
p2m_export "AlgebraicCurve.Place" "isUnit_mk_of_ord_eq_zero"

private theorem _root_.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)
p2m_export "AlgebraicCurve.Place" "residue_ne_zero_of_ord_eq_zero"

private theorem _root_.AlgebraicCurve.Place.evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_of_ord_nonneg hf h.ge)
  rw [h0, map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm
p2m_export "AlgebraicCurve.Place" "evalAt_ne_zero"

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]
p2m_export "AlgebraicCurve.Place" "evalAt_algebraMap"
end Place
namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree"
p2m_open "AlgebraicCurve.Divisor"
end Divisor
end AlgebraicCurve

open Polynomial IntermediateField
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Place.ord_neg"
p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg"
end AlgebraicCurve
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Place.ord_neg"
namespace KummerCover
p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg"
section Roots
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {L : Type*} [Field L] [Algebra K L]
end Roots
section Swap
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} {f : F} {α : L}

private theorem forall_pow_ne_mul_pow (hf : ∀ g : F, g ^ p ≠ f) {h : F} (hh : h ≠ 0) :
    ∀ g : F, g ^ p ≠ f * h ^ p := by
  intro g hg
  apply hf (g / h)
  rw [div_pow, hg, mul_div_cancel_right₀ _ (pow_ne_zero p hh)]

private theorem mul_algebraMap_pow_eq (hα : α ^ p = algebraMap F L f) (h : F) :
    (α * algebraMap F L h) ^ p = algebraMap F L (f * h ^ p) := by
  rw [mul_pow, hα, ← map_pow, ← map_mul]

private theorem adjoin_mul_algebraMap_eq_top (htop : F⟮α⟯ = ⊤) {h : F} (hh : h ≠ 0) :
    F⟮α * algebraMap F L h⟯ = ⊤ := by
  rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
  have h1 := mem_adjoin_simple_self F (α * algebraMap F L h)
  have h2 : algebraMap F L h⁻¹ ∈ F⟮α * algebraMap F L h⟯ := IntermediateField.algebraMap_mem _ _
  have h3 := mul_mem h1 h2
  rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hh, map_one, mul_one] at h3

private theorem not_mem_range_of_pow_eq (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f) :
    α ∉ Set.range (algebraMap F L) := by
  rintro ⟨a, rfl⟩
  rw [← map_pow] at hα
  exact hf a ((algebraMap F L).injective hα)

private theorem sub_algebraMap_ne_zero (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f)
    (c : F) : α - algebraMap F L c ≠ 0 := fun h =>
  not_mem_range_of_pow_eq hf hα ⟨c, (sub_eq_zero.mp h).symm⟩
end Swap
section Pure
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}
private theorem irreducible_X_pow_sub_C (hf : ∀ g : F, g ^ p ≠ f) : Irreducible (X ^ p - C f) :=
  X_pow_sub_C_irreducible_of_prime hp.out hf
private theorem ne_zero_of_forall_pow_ne (hf : ∀ g : F, g ^ p ≠ f) : f ≠ 0 := by
  rintro rfl
  exact hf 0 (zero_pow hp.out.ne_zero)
private theorem isIntegral_of_pow_eq (hα : α ^ p = algebraMap F L f) : IsIntegral F α :=
  IsIntegral.of_pow hp.out.pos (hα ▸ isIntegral_algebraMap)

private theorem minpoly_eq_of_pow_eq (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f) :
    minpoly F α = X ^ p - C f :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C hf)
    (by simp only [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self])
    (monic_X_pow_sub_C f hp.out.ne_zero)).symm

private theorem norm_root_sub_algebraMap (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f)
    (htop : F⟮α⟯ = ⊤) (c : F) :
    Algebra.norm F (α - algebraMap F L c) = (-1) ^ p * (c ^ p - f) := by
  have hxint : IsIntegral F (α - algebraMap F L c) :=
    (isIntegral_of_pow_eq hα).sub isIntegral_algebraMap
  have hminx : minpoly F (α - algebraMap F L c) = (X ^ p - C f).comp (X + C c) := by
    rw [minpoly.sub_algebraMap, minpoly_eq_of_pow_eq hf hα]
  have hxtop : F⟮α - algebraMap F L c⟯ = ⊤ := by
    rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
    have h1 : α - algebraMap F L c ∈ F⟮α - algebraMap F L c⟯ := mem_adjoin_simple_self F _
    have h2 : algebraMap F L c ∈ F⟮α - algebraMap F L c⟯ := IntermediateField.algebraMap_mem _ c
    simpa using add_mem h1 h2
  let pb : PowerBasis F L := (adjoin.powerBasis hxint).map ((equivOfEq hxtop).trans topEquiv)
  have hgen : pb.gen = α - algebraMap F L c := by
    simp only [pb, PowerBasis.map_gen, adjoin.powerBasis_gen, AlgEquiv.trans_apply]
    rfl
  have hdim : pb.dim = p := by
    simp only [pb, PowerBasis.map_dim, adjoin.powerBasis_dim, hminx, natDegree_comp,
      natDegree_X_pow_sub_C, natDegree_X_add_C, mul_one]
  have key := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hgen, hdim, hminx] at key
  rw [key, coeff_zero_eq_eval_zero, eval_comp]
  simp only [eval_add, eval_X, eval_C, zero_add, eval_sub, eval_pow]
end Pure
section Split
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F}
variable [IsSplittingField F L (X ^ p - C f)]
end Split
section Model
variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] {f : F}
end Model
section OrdNorm
variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}

private theorem ord_norm_root_sub_algebraMap (v : Place K F) (hf : ∀ g : F, g ^ p ≠ f)
    (hα : α ^ p = algebraMap F L f) (htop : F⟮α⟯ = ⊤) (c : F) :
    v.ord (Algebra.norm F (α - algebraMap F L c)) = v.ord (f - c ^ p) := by
  rw [norm_root_sub_algebraMap hf hα htop c]
  rcases neg_one_pow_eq_or F p with h | h <;> rw [h]
  · rw [one_mul, ← neg_sub, v.ord_neg]
  · rw [neg_one_mul, neg_sub]
end OrdNorm
end AlgebraicCurve.KummerCover
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Place.ord_neg"
p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation_coe_eq_one_iff ord ord_zero ord_mul ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring ramificationIndex ramificationIndex_pos restrict ord_restrict inertiaDeg IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt ord_neg fiberOver mem_fiberOver restrict_mem_fiberOver ord_eq_zero_iff_adicValuation_eq_one ord_nonneg_of_mem exists_ord_eq_one ord_norm_eq_sum_fiberOver_of_isSeparable inertiaDeg_pos ord_algebraMap"
p2m_open "AlgebraicCurve.Place~mem_of_ord_nonneg"
variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L]
  [IsScalarTower K F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]

private theorem ord_le_ord_norm_of_forall_ord_nonneg (v : Place K F) {x : L} (hx : x ≠ 0)
    (hnonneg : ∀ w' ∈ v.fiberOver L, 0 ≤ w'.ord x) {w : Place K L} (hw : w ∈ v.fiberOver L) :
    w.ord x ≤ v.ord (Algebra.norm F x) := by
  rw [v.ord_norm_eq_sum_fiberOver_of_isSeparable hx]
  calc w.ord x ≤ (w.inertiaDeg F : ℤ) * w.ord x :=
        le_mul_of_one_le_left (hnonneg w hw) (by exact_mod_cast w.inertiaDeg_pos (F := F))
    _ ≤ ∑ w' ∈ v.fiberOver L, (w'.inertiaDeg F : ℤ) * w'.ord x :=
        Finset.single_le_sum (f := fun w' => (w'.inertiaDeg F : ℤ) * w'.ord x)
          (fun w' hw' => mul_nonneg (by positivity) (hnonneg w' hw')) hw

private theorem ord_le_ord_norm_of_forall_ord_nonneg' {x : L} (hx : x ≠ 0) (w : Place K L)
    (hnonneg : ∀ w' : Place K L, w'.restrict F = w.restrict F → 0 ≤ w'.ord x) :
    w.ord x ≤ (w.restrict F).ord (Algebra.norm F x) :=
  ord_le_ord_norm_of_forall_ord_nonneg (w.restrict F) hx
    (fun w' hw' => hnonneg w' ((mem_fiberOver _).mp hw')) (restrict_mem_fiberOver w)
section ResidueGeomSum
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem residue_mk_algebraMap (a : K) :
    residue v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩
      = algebraMap K v.ResidueField a := rfl

private theorem residue_geom_sum₂_of_residue_eq {x y : F} (hx : x ∈ v.toValuationSubring)
    (hy : y ∈ v.toValuationSubring) {r : v.ResidueField}
    (hxr : residue v.toValuationSubring ⟨x, hx⟩ = r)
    (hyr : residue v.toValuationSubring ⟨y, hy⟩ = r) (n : ℕ)
    (hS : (∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j)) ∈ v.toValuationSubring) :
    residue v.toValuationSubring ⟨∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j), hS⟩
      = n * r ^ (n - 1) := by
  have hcoe : (⟨∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j), hS⟩ : v.toValuationSubring)
      = ∑ j ∈ Finset.range n, (⟨x, hx⟩ : v.toValuationSubring) ^ j
          * (⟨y, hy⟩ : v.toValuationSubring) ^ (n - 1 - j) := by
    apply Subtype.ext
    push_cast
    rfl
  rw [hcoe, map_sum]
  simp only [map_mul, map_pow, hxr, hyr]
  exact geom_sum₂_self r n
end ResidueGeomSum
section Normalize
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem exists_ord_mul_pow_eq_zero (v : Place K F) {p : ℕ} {f : F} (hf0 : f ≠ 0)
    (hord : (p : ℤ) ∣ v.ord f) : ∃ h : F, h ≠ 0 ∧ v.ord (f * h ^ p) = 0 := by
  obtain ⟨t, ht⟩ := v.exists_ord_eq_one
  obtain ⟨m, hm⟩ := hord
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [ord_zero] at ht
    exact zero_ne_one ht
  refine ⟨t ^ (-m), zpow_ne_zero _ ht0, ?_⟩
  rw [v.ord_mul hf0 (pow_ne_zero _ (zpow_ne_zero _ ht0)), ← zpow_natCast, ← zpow_mul,
    v.ord_zpow, ht, hm]
  ring
end Normalize
section FibreUnit
variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L]
  [IsScalarTower K F L] [Algebra.IsIntegral F L]

private theorem ord_eq_zero_of_pow_eq_of_ord_restrict_eq_zero (w : Place K L) {p : ℕ} (hp : p ≠ 0)
    {f₁ : F} {β : L} (hβ : β ^ p = algebraMap F L f₁) (h0 : (w.restrict F).ord f₁ = 0) :
    w.ord β = 0 := by
  have h := w.ord_restrict (F := F) f₁
  rw [h0, mul_zero, ← hβ, ← zpow_natCast, w.ord_zpow] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hp)
end FibreUnit
section OrdResidueKit
open IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_iff_isUnit {g : F} (hg : g ≠ 0) (hmem : g ∈ v.toValuationSubring) :
    v.ord g = 0 ↔ IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
  rw [v.ord_eq_zero_iff_adicValuation_eq_one hg]
  exact v.adicValuation_coe_eq_one_iff ⟨g, hmem⟩
p2m_export "AlgebraicCurve.Place" "ord_eq_zero_iff_isUnit"

private theorem ord_eq_zero_of_residue_ne_zero {g : F} (hg : g ≠ 0) (hmem : g ∈ v.toValuationSubring)
    (hres : residue v.toValuationSubring ⟨g, hmem⟩ ≠ 0) :
    v.ord g = 0 := by
  refine (v.ord_eq_zero_iff_isUnit hg hmem).mpr ?_
  by_contra hnotunit
  apply hres
  have : ¬IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := hnotunit
  rwa [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    ← Ideal.Quotient.eq_zero_iff_mem] at this

private theorem _root_.AlgebraicCurve.Place.one_le_ord_of_residue_eq_zero {g : F} (hg : g ≠ 0) (hmem : g ∈ v.toValuationSubring)
    (hres : residue v.toValuationSubring ⟨g, hmem⟩ = 0) :
    1 ≤ v.ord g := by
  have hnonunit : ¬IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hres
  have hne : v.ord g ≠ 0 := fun h => hnonunit ((v.ord_eq_zero_iff_isUnit hg hmem).mp h)
  have hnn : 0 ≤ v.ord g := v.ord_nonneg_of_mem hmem
  omega
p2m_export "AlgebraicCurve.Place" "one_le_ord_of_residue_eq_zero"

private theorem one_le_ord_sub_evalAt (hv : v.IsRational) {f : F} (hf : f ≠ 0) (hord : v.ord f = 0)
    (hfc : f ≠ algebraMap K F (v.evalAt f)) :
    1 ≤ v.ord (f - algebraMap K F (v.evalAt f)) := by
  set c := v.evalAt f
  have hfmem : f ∈ v.toValuationSubring := v.mem_of_ord_nonneg hf hord.ge
  have hcmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsubmem : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hfmem hcmem
  refine v.one_le_ord_of_residue_eq_zero (sub_ne_zero.mpr hfc) hsubmem ?_
  have h1 : residue v.toValuationSubring ⟨f, hfmem⟩ = algebraMap K _ c :=
    (v.algebraMap_evalAt hv hfmem).symm
  have h2 : residue v.toValuationSubring ⟨algebraMap K F c, hcmem⟩ = algebraMap K _ c := by
    have := (v.algebraMap_evalAt hv hcmem)
    rwa [v.evalAt_algebraMap c] at this
  calc residue v.toValuationSubring ⟨f - algebraMap K F c, hsubmem⟩
      = residue v.toValuationSubring (⟨f, hfmem⟩ - ⟨algebraMap K F c, hcmem⟩) := by congr 1
    _ = residue v.toValuationSubring ⟨f, hfmem⟩
        - residue v.toValuationSubring ⟨algebraMap K F c, hcmem⟩ := map_sub _ _ _
    _ = 0 := by rw [h1, h2]; ring
end OrdResidueKit
section CoverLemma
open IsLocalRing
variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
variable {p : ℕ} [Fact p.Prime] {f : F} {α : L}
end CoverLemma
end Place
section ConstantsAlg
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
end ConstantsAlg
section ConstantsOrd
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
end ConstantsOrd
end AlgebraicCurve

p2m_open "AlgebraicCurve~Place.mem_of_ord_nonneg" in p2m_open "AlgebraicCurve.Place~mem_of_ord_nonneg" in open _root_.P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable.AlgebraicCurve.Place in
theorem solution {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {p : ℕ} [Fact p.Prime] {f : F} {α : L}
    (hf : ∀ g : F, g ^ p ≠ f)
    (hα : α ^ p = algebraMap F L f) (htop : F⟮α⟯ = ⊤)
    (hord : ∀ v : Place K F, (p : ℤ) ∣ v.ord f)
    (w : Place K L) (hw_rat : w.IsRational) :
    w.ramificationIndex F = 1 := by
  set v := w.restrict F

  obtain ⟨h, hh0, hf1ord⟩ :=
    exists_ord_mul_pow_eq_zero v (KummerCover.ne_zero_of_forall_pow_ne hf) (hord v)
  set f₁ := f * h ^ p with hf1def
  set β := α * algebraMap F L h with hβdef
  have hf₁ : ∀ g : F, g ^ p ≠ f₁ := KummerCover.forall_pow_ne_mul_pow hf hh0
  have hβ : β ^ p = algebraMap F L f₁ := KummerCover.mul_algebraMap_pow_eq hα h
  have hβtop : F⟮β⟯ = ⊤ := KummerCover.adjoin_mul_algebraMap_eq_top htop hh0
  have hβne : β ≠ 0 := by
    intro hz; apply KummerCover.ne_zero_of_forall_pow_ne hf₁
    have := hβ; rw [hz, zero_pow (Fact.out : p.Prime).ne_zero] at this
    exact ((algebraMap F L).injective (this.symm.trans (map_zero _).symm))

  have hβord0 : w.ord β = 0 :=
    ord_eq_zero_of_pow_eq_of_ord_restrict_eq_zero w (Fact.out : p.Prime).ne_zero hβ hf1ord

  set c := w.evalAt β
  have hc0 : c ≠ 0 := w.evalAt_ne_zero hw_rat hβne hβord0
  have hβc : β ≠ algebraMap K L c := by
    intro heq
    exact KummerCover.sub_algebraMap_ne_zero hf₁ hβ (algebraMap K F c)
      (by rw [← IsScalarTower.algebraMap_apply K F L, ← heq]; ring)
  have hβc' : β ≠ algebraMap F L (algebraMap K F c) := by
    rw [← IsScalarTower.algebraMap_apply K F L]; exact hβc
  set cL := algebraMap K L c with hcLdef
  have hcLord : w.ord cL = 0 := w.ord_algebraMap c
  have hm0ge : 1 ≤ w.ord (β - cL) := by
    have := one_le_ord_sub_evalAt w hw_rat hβne hβord0 hβc
    simpa [hcLdef] using this
  set m₀ := w.ord (β - cL) with hm0def

  set cF := algebraMap K F c with hcFdef
  set S : L := ∑ j ∈ Finset.range p, β ^ j * cL ^ (p - 1 - j) with hSdef
  have hfact : β ^ p - cL ^ p = (β - cL) * S :=
    ((Commute.all β cL).mul_geom_sum₂ p).symm
  have hcLmem : cL ∈ w.toValuationSubring := w.algebraMap_mem' c
  have hβmem : β ∈ w.toValuationSubring := w.mem_of_ord_nonneg hβne hβord0.ge
  have hSmem : S ∈ w.toValuationSubring := by
    refine Subring.sum_mem _ fun j _ => ?_
    exact mul_mem (pow_mem hβmem _) (pow_mem hcLmem _)
  have hSres :
      residue w.toValuationSubring ⟨S, hSmem⟩ = (p : w.ResidueField) * algebraMap K _ c ^ (p - 1) := by
    have hβres : residue w.toValuationSubring ⟨β, hβmem⟩ = algebraMap K w.ResidueField c :=
      (w.algebraMap_evalAt hw_rat hβmem).symm
    have hcLres : residue w.toValuationSubring ⟨cL, hcLmem⟩ = algebraMap K w.ResidueField c := by
      have hmk : (⟨cL, hcLmem⟩ : w.toValuationSubring)
          = ⟨algebraMap K L c, w.algebraMap_mem' c⟩ := Subtype.ext hcLdef
      rw [hmk]; exact residue_mk_algebraMap w c
    exact residue_geom_sum₂_of_residue_eq w hβmem hcLmem hβres hcLres p hSmem

  have hpF : (p : F) ≠ 0 := by
    intro hp0
    have hsep : (X ^ p - C f : F[X]).Separable := by
      rw [← KummerCover.minpoly_eq_of_pow_eq hf hα]
      exact Algebra.IsSeparable.isSeparable F α
    have hder : Polynomial.derivative (X ^ p - C f : F[X]) = 0 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, hp0,
        map_zero, zero_mul, sub_zero]
    rw [Polynomial.separable_def, hder, isCoprime_zero_right] at hsep
    exact (KummerCover.irreducible_X_pow_sub_C hf).not_isUnit hsep
  have hpK : (p : K) ≠ 0 := fun hp0 =>
    hpF (by rw [← map_natCast (algebraMap K F) p, hp0, map_zero])
  have hpκ : (p : w.ResidueField) ≠ 0 := fun hp0 =>
    hpK ((algebraMap K w.ResidueField).injective (by rw [map_natCast, map_zero]; exact hp0))
  have hSresne : residue w.toValuationSubring ⟨S, hSmem⟩ ≠ 0 := by
    rw [hSres]
    refine mul_ne_zero hpκ (pow_ne_zero _ ?_)
    exact (map_ne_zero_iff _ (algebraMap K w.ResidueField).injective).mpr hc0
  have hSne : S ≠ 0 := by
    intro hz; apply hSresne
    have : (⟨S, hSmem⟩ : w.toValuationSubring) = 0 := Subtype.ext hz
    simp [this]
  have hSord : w.ord S = 0 := ord_eq_zero_of_residue_ne_zero w hSne hSmem hSresne

  set f₂ := f₁ - cF ^ p with hf2def
  have hf2ne : f₂ ≠ 0 := by
    intro hz
    exact hf₁ cF (sub_eq_zero.mp hz).symm
  set K₀ := v.ord f₂ with hK0def
  have hkey : algebraMap F L f₂ = β ^ p - cL ^ p := by
    simp only [hf2def, map_sub, map_pow, ← hβ, hcLdef, hcFdef,
      ← IsScalarTower.algebraMap_apply K F L]
  have heK : (w.ramificationIndex F : ℤ) * K₀ = m₀ := by
    have hordrest := w.ord_restrict (F := F) f₂
    rw [hkey, hfact] at hordrest
    have hβcne : β - cL ≠ 0 := sub_ne_zero.mpr hβc
    rw [w.ord_mul hβcne hSne, hSord, add_zero] at hordrest
    simpa [hK0def, hm0def, v] using hordrest.symm

  have hβcLne : β - cL ≠ 0 := sub_ne_zero.mpr hβc
  have hcLeq : cL = algebraMap F L cF := by
    simp only [hcLdef, hcFdef, IsScalarTower.algebraMap_apply K F L]
  have hK0_eq_ordnorm : K₀ = v.ord (Algebra.norm F (β - cL)) := by
    rw [hcLeq, KummerCover.ord_norm_root_sub_algebraMap v hf₁ hβ hβtop cF, hK0def, hf2def]
  have hKge : m₀ ≤ K₀ := by
    rw [hK0_eq_ordnorm, hm0def]
    refine ord_le_ord_norm_of_forall_ord_nonneg' hβcLne w (fun w' hw' => ?_)

    have hβord0' : w'.ord β = 0 :=
      ord_eq_zero_of_pow_eq_of_ord_restrict_eq_zero w' (Fact.out : p.Prime).ne_zero hβ
        (by rw [hw']; exact hf1ord)
    have hβmem' : β ∈ w'.toValuationSubring := w'.mem_of_ord_nonneg hβne hβord0'.ge
    have hcLmem' : cL ∈ w'.toValuationSubring := hcLdef ▸ w'.algebraMap_mem' c
    exact w'.ord_nonneg_of_mem (sub_mem hβmem' hcLmem')

  have hepos : 0 < w.ramificationIndex F := w.ramificationIndex_pos (F := F)
  have hK0pos : 1 ≤ K₀ := by nlinarith [hm0ge, heK, hepos]
  have : (w.ramificationIndex F : ℤ) ≤ 1 := by
    have := heK.symm ▸ hKge
    nlinarith [hK0pos]
  omega

#print axioms solution

end S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable (solution)
