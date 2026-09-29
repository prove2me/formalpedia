-- Prove2me | solution 1 for AlgebraicCurve.Place.natCard_setOf_comap_eq_eq_deg_of_linearDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/fda55748-a4ae-5dcd-af1c-2114f1d72ea5

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap IsCurveOver IsCurveOver.finiteResidue IsCurveOver.exists_separating_transcendental Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable Place.mem_iff_ord_nonneg Place.mk_mem_maximalIdeal_iff"
p2m_open "AlgebraicCurve"
namespace CFEFibre

section ValSub

variable {L : Type*} [Field L]

theorem inv_notMem_of_mem_nonunits (B : ValuationSubring L) {x : L} (hx0 : x ≠ 0)
    (hx : x ∈ B.nonunits) : x⁻¹ ∉ B := by
  rw [ValuationSubring.mem_nonunits_iff] at hx
  rw [← ValuationSubring.valuation_le_one_iff, not_le]
  have h := (Valuation.one_lt_val_iff B.valuation (inv_ne_zero hx0)).mpr
  rw [inv_inv] at h
  exact h hx

theorem mem_nonunits_of_inv_notMem (B : ValuationSubring L) {x : L} (hx : x⁻¹ ∉ B) :
    x ∈ B.nonunits := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by rw [inv_zero]; exact B.zero_mem)
  rw [ValuationSubring.mem_nonunits_iff]
  rw [← ValuationSubring.valuation_le_one_iff, not_le] at hx
  have h := (Valuation.one_lt_val_iff B.valuation (inv_ne_zero hx0)).mp
  rw [inv_inv] at h
  exact h hx

theorem mem_nonunits_iff_inv_notMem (B : ValuationSubring L) {x : L} (hx0 : x ≠ 0) :
    x ∈ B.nonunits ↔ x⁻¹ ∉ B :=
  ⟨inv_notMem_of_mem_nonunits B hx0, mem_nonunits_of_inv_notMem B⟩

theorem zero_mem_nonunits (B : ValuationSubring L) : (0 : L) ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]
  exact zero_lt_one

theorem sub_mem_nonunits (B : ValuationSubring L) {x y : L} (hx : x ∈ B.nonunits)
    (hy : y ∈ B.nonunits) : x - y ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx hy ⊢
  exact lt_of_le_of_lt (Valuation.map_sub _ x y) (max_lt hx hy)

theorem add_mem_nonunits (B : ValuationSubring L) {x y : L} (hx : x ∈ B.nonunits)
    (hy : y ∈ B.nonunits) : x + y ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx hy ⊢
  exact lt_of_le_of_lt (Valuation.map_add _ x y) (max_lt hx hy)

theorem mul_mem_nonunits (B : ValuationSubring L) {b x : L} (hb : b ∈ B)
    (hx : x ∈ B.nonunits) : b * x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hb
  rw [map_mul]
  calc B.valuation b * B.valuation x ≤ 1 * B.valuation x := mul_le_mul_left hb _
    _ = B.valuation x := one_mul _
    _ < 1 := hx

theorem valuation_eq_one_of_notMem_nonunits (B : ValuationSubring L) {x : L} (hxB : x ∈ B)
    (hx : x ∉ B.nonunits) : B.valuation x = 1 := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hx
  rw [← ValuationSubring.valuation_le_one_iff] at hxB
  exact le_antisymm hxB hx

theorem mul_notMem_nonunits (B : ValuationSubring L) {x y : L} (hxB : x ∈ B) (hyB : y ∈ B)
    (hx : x ∉ B.nonunits) (hy : y ∉ B.nonunits) : x * y ∉ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_mul, valuation_eq_one_of_notMem_nonunits B hxB hx,
    valuation_eq_one_of_notMem_nonunits B hyB hy, one_mul]
  exact lt_irrefl 1

theorem ne_zero_of_notMem_nonunits (B : ValuationSubring L) {x : L} (hx : x ∉ B.nonunits) :
    x ≠ 0 := by
  rintro rfl
  exact hx (zero_mem_nonunits B)

theorem nonunits_le (B : ValuationSubring L) {x : L} (hx : x ∈ B.nonunits) : x ∈ B :=
  ValuationSubring.nonunits_subset hx

theorem mk_mem_maximalIdeal_iff_mem_nonunits (B : ValuationSubring L) {x : L} (hx : x ∈ B) :
    (⟨x, hx⟩ : B) ∈ maximalIdeal B ↔ x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩

theorem isUnit_mk_of_notMem_nonunits (B : ValuationSubring L) {x : L} (hxB : x ∈ B)
    (hx : x ∉ B.nonunits) : IsUnit (⟨x, hxB⟩ : B) := by
  by_contra h
  exact hx ((mk_mem_maximalIdeal_iff_mem_nonunits B hxB).mp
    ((IsLocalRing.mem_maximalIdeal _).mpr h))

end ValSub

section Residue

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem eq_zero_of_algebraMap_mem_nonunits (W : Place K F) {a : K}
    (ha : algebraMap K F a ∈ W.toValuationSubring.nonunits) : a = 0 := by
  by_contra h0
  have hne : algebraMap K F a ≠ 0 := by simpa using h0
  apply inv_notMem_of_mem_nonunits _ hne ha
  rw [← map_inv₀]
  exact W.algebraMap_mem' _

def ResBij (W : Place K F) : Prop := Function.Bijective (algebraMap K W.ResidueField)

theorem resBij_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (W : Place K F) : ResBij W := by
  haveI : Module.Finite K W.ResidueField := IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral K W.ResidueField := Algebra.IsIntegral.of_finite K W.ResidueField
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

def resHom (W : Place K F) (hW : ResBij W) : W.toValuationSubring →ₐ[K] K :=
  { ((RingEquiv.ofBijective (algebraMap K W.ResidueField) hW).symm.toRingHom.comp
      (IsLocalRing.residue W.toValuationSubring)) with
    commutes' := fun a => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        Function.comp_apply]
      apply (RingEquiv.ofBijective (algebraMap K W.ResidueField) hW).injective
      rw [RingEquiv.apply_symm_apply]
      rfl }

theorem resHom_apply (W : Place K F) (hW : ResBij W) (g : W.toValuationSubring) :
    resHom W hW g = (RingEquiv.ofBijective (algebraMap K W.ResidueField) hW).symm
      (IsLocalRing.residue _ g) := rfl

theorem algebraMap_resHom (W : Place K F) (hW : ResBij W) (g : W.toValuationSubring) :
    algebraMap K W.ResidueField (resHom W hW g) = IsLocalRing.residue _ g := by
  rw [resHom_apply]
  exact (RingEquiv.ofBijective (algebraMap K W.ResidueField) hW).apply_symm_apply _

theorem resHom_spec (W : Place K F) (hW : ResBij W) (g : W.toValuationSubring) :
    (g : F) - algebraMap K F (resHom W hW g) ∈ W.toValuationSubring.nonunits := by
  set a := resHom W hW g with ha
  have hmem : g - algebraMap K W.toValuationSubring a ∈ maximalIdeal W.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    change IsLocalRing.residue _ g - algebraMap K W.ResidueField a = 0
    rw [algebraMap_resHom, sub_self]
  have := (mk_mem_maximalIdeal_iff_mem_nonunits W.toValuationSubring
    (g - algebraMap K W.toValuationSubring a).2).mp (by first | exact hmem | simpa using hmem)
  simpa [Place.coe_algebraMap] using this

theorem resHom_eq_iff (W : Place K F) (hW : ResBij W) (g : W.toValuationSubring) (a : K) :
    resHom W hW g = a ↔ (g : F) - algebraMap K F a ∈ W.toValuationSubring.nonunits := by
  constructor
  · rintro rfl
    exact resHom_spec W hW g
  · intro h
    have h1 := resHom_spec W hW g
    have h2 := sub_mem_nonunits _ h h1
    have h3 : algebraMap K F (resHom W hW g - a) ∈ W.toValuationSubring.nonunits := by
      rw [map_sub]
      convert h2 using 1
      ring
    have := eq_zero_of_algebraMap_mem_nonunits W h3
    exact (sub_eq_zero.mp this)

theorem mem_nonunits_iff_resHom_eq_zero (W : Place K F) (hW : ResBij W)
    (g : W.toValuationSubring) :
    (g : F) ∈ W.toValuationSubring.nonunits ↔ resHom W hW g = 0 := by
  rw [resHom_eq_iff, map_zero, sub_zero]

theorem coe_aeval_mk (W : Place K F) {x : F} (hx : x ∈ W.toValuationSubring) (P : K[X]) :
    ((aeval (⟨x, hx⟩ : W.toValuationSubring) P : W.toValuationSubring) : F) = aeval x P := by
  have := aeval_algebraMap_apply F (⟨x, hx⟩ : W.toValuationSubring) P
  exact this.symm

theorem aeval_mem (W : Place K F) {x : F} (hx : x ∈ W.toValuationSubring) (P : K[X]) :
    aeval x P ∈ W.toValuationSubring := by
  rw [← coe_aeval_mk W hx P]
  exact Subtype.mem _

theorem resHom_aeval (W : Place K F) (hW : ResBij W) {x : F} (hx : x ∈ W.toValuationSubring)
    (P : K[X]) :
    resHom W hW ⟨aeval x P, aeval_mem W hx P⟩ = P.eval (resHom W hW ⟨x, hx⟩) := by
  have h1 : (⟨aeval x P, aeval_mem W hx P⟩ : W.toValuationSubring)
      = aeval (⟨x, hx⟩ : W.toValuationSubring) P := by
    apply Subtype.ext
    rw [coe_aeval_mk]
  rw [h1, ← aeval_algHom_apply, coe_aeval_eq_eval]

end Residue

section Over

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

def Over (v : Place k F₀) (W : Place K F) : Prop :=
  W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring

theorem mem_iff_of_over {v : Place k F₀} {W : Place K F} (hW : Over v W) (f : F₀) :
    f ∈ v.toValuationSubring ↔ algebraMap F₀ F f ∈ W.toValuationSubring := by
  rw [← ValuationSubring.mem_comap, show W.toValuationSubring.comap (algebraMap F₀ F)
    = v.toValuationSubring from hW]

theorem nonunits_iff_of_over {v : Place k F₀} {W : Place K F} (hW : Over v W) (f : F₀) :
    algebraMap F₀ F f ∈ W.toValuationSubring.nonunits ↔ f ∈ v.toValuationSubring.nonunits := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [map_zero]
    exact ⟨fun _ => zero_mem_nonunits _, fun _ => zero_mem_nonunits _⟩
  · rw [mem_nonunits_iff_inv_notMem _ hf,
      mem_nonunits_iff_inv_notMem _ ((map_ne_zero (algebraMap F₀ F)).mpr hf), ← map_inv₀,
      ← mem_iff_of_over hW]

end Over

section ResidueData

variable {k F₀ : Type*} [Field k] [Field F₀] [Algebra k F₀]

def residueₐ (v : Place k F₀) : v.toValuationSubring →ₐ[k] v.ResidueField :=
  { IsLocalRing.residue v.toValuationSubring with commutes' := fun _ => rfl }

@[scoped simp] theorem residueₐ_apply (v : Place k F₀) (x : v.toValuationSubring) :
    residueₐ v x = IsLocalRing.residue _ x := rfl

theorem residue_aeval (v : Place k F₀) (θ : v.toValuationSubring) (P : k[X]) :
    IsLocalRing.residue _ (aeval θ P) = aeval (IsLocalRing.residue _ θ) P := by
  rw [← residueₐ_apply, ← aeval_algHom_apply]
  rfl

theorem exists_poly_add_mul (v : Place k F₀) [Module.Finite k v.ResidueField]
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤) (f : v.toValuationSubring) :
    ∃ P : k[X], ∃ g : v.toValuationSubring, f = aeval θ P + π * g := by
  set θb := IsLocalRing.residue _ θ with hθb
  have hint : IsIntegral k θb := IsIntegral.of_finite k θb
  have hmem : IsLocalRing.residue _ f ∈ (aeval (R := k) θb).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
      ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]
    trivial
  obtain ⟨P, hP⟩ := hmem
  have hdiff : f - aeval θ P ∈ maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, residue_aeval, ← hθb]
    change IsLocalRing.residue _ f - aeval θb P = 0
    have hP' : aeval θb P = IsLocalRing.residue _ f := hP
    rw [hP', sub_self]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hdiff
  obtain ⟨g, hg⟩ := hdiff
  exact ⟨P, g, by rw [mul_comm] at hg; rw [hg]; ring⟩

theorem aeval_minpoly_mem (v : Place k F₀) (θ : v.toValuationSubring) :
    aeval θ (minpoly k (IsLocalRing.residue _ θ)) ∈ maximalIdeal v.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, minpoly.aeval]

theorem exists_aeval_minpoly_eq (v : Place k F₀) {θ π : v.toValuationSubring}
    (hπ : Irreducible π) :
    ∃ g : v.toValuationSubring, aeval θ (minpoly k (IsLocalRing.residue _ θ)) = π * g := by
  have h := aeval_minpoly_mem v θ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [← hg, mul_comm]⟩

theorem natDegree_minpoly_eq_deg (v : Place k F₀) [Module.Finite k v.ResidueField]
    {θ : v.toValuationSubring}
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤) :
    (minpoly k (IsLocalRing.residue _ θ)).natDegree = v.deg := by
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  rw [← IntermediateField.adjoin.finrank hint, hθ]
  change Module.finrank k (⊤ : IntermediateField k v.ResidueField) = Module.finrank k v.ResidueField
  exact IntermediateField.finrank_top'

theorem coe_aeval (v : Place k F₀) (θ : v.toValuationSubring) (P : k[X]) :
    ((aeval θ P : v.toValuationSubring) : F₀) = aeval (θ : F₀) P :=
  (aeval_algebraMap_apply F₀ θ P).symm

theorem coeff_eq_zero_of_sum_smul_pow_mem (v : Place k F₀) (θ : v.toValuationSubring)
    (a : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree → k)
    (h : v.toValuationSubring.valuation (∑ i, a i • (θ : F₀) ^ (i : ℕ)) < 1) :
    ∀ i, a i = 0 := by
  have hcoe : ((∑ i, a i • θ ^ (i : ℕ) : v.toValuationSubring) : F₀)
      = ∑ i, a i • (θ : F₀) ^ (i : ℕ) := by
    push_cast
    simp [Algebra.smul_def]
  have hmax : (∑ i, a i • θ ^ (i : ℕ) : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [ValuationSubring.valuation_lt_one_iff, hcoe]
    exact h
  have hres : residueₐ v (∑ i, a i • θ ^ (i : ℕ)) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have hsum : ∑ i, a i • (IsLocalRing.residue _ θ) ^ (i : ℕ) = 0 := by
    rw [map_sum] at hres
    simpa [map_smul, map_pow] using hres
  exact Fintype.linearIndependent_iff.mp (linearIndependent_pow (IsLocalRing.residue _ θ)) a hsum

end ResidueData

section RingR

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

local notation "ι" => algebraMap F₀ F

variable (K F) in

def Rv (v : Place k F₀) : Subalgebra K F :=
  Algebra.adjoin K (algebraMap F₀ F '' (v.toValuationSubring : Set F₀))

theorem algebraMap_mem_Rv (v : Place k F₀) {f : F₀} (hf : f ∈ v.toValuationSubring) :
    ι f ∈ Rv K F v :=
  Algebra.subset_adjoin ⟨f, hf, rfl⟩

theorem coe_mem_Rv (v : Place k F₀) (f : v.toValuationSubring) : ι (f : F₀) ∈ Rv K F v :=
  algebraMap_mem_Rv v f.2

theorem aeval_mem_Rv (v : Place k F₀) {x : F} (hx : x ∈ Rv K F v) (P : K[X]) :
    aeval x P ∈ Rv K F v := by
  have h : Algebra.adjoin K {x} ≤ Rv K F v := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  exact h (aeval_mem_adjoin_singleton K x)

theorem Rv_le_of_over {v : Place k F₀} {W : Place K F} (hW : Over v W) {x : F}
    (hx : x ∈ Rv K F v) : x ∈ W.toValuationSubring := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact (mem_iff_of_over hW f).mp hf
  | algebraMap r => exact W.algebraMap_mem' r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem algebraMap_coe_aeval (v : Place k F₀) (θ : v.toValuationSubring) (P : k[X]) :
    ι ((aeval θ P : v.toValuationSubring) : F₀) = aeval (ι (θ : F₀)) (P.map (algebraMap k K)) := by
  rw [coe_aeval, aeval_map_algebraMap,
    show ι (θ : F₀) = (IsScalarTower.toAlgHom k F₀ F) (θ : F₀) from rfl, aeval_algHom_apply]
  rfl

theorem exists_decomp (v : Place k F₀) [Module.Finite k v.ResidueField]
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤) {r : F} (hr : r ∈ Rv K F v) :
    ∃ P : K[X], ∃ r' ∈ Rv K F v, r = aeval (ι (θ : F₀)) P + ι (π : F₀) * r' := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      obtain ⟨P, g, hfg⟩ := exists_poly_add_mul v hπ hθ ⟨f, hf⟩
      have hcoe : f = ((aeval θ P : v.toValuationSubring) : F₀) + (π : F₀) * (g : F₀) := by
        have := congrArg Subtype.val hfg
        simpa using this
      refine ⟨P.map (algebraMap k K), ι (g : F₀), coe_mem_Rv v g, ?_⟩
      rw [hcoe, map_add, map_mul, algebraMap_coe_aeval (K := K)]
  | algebraMap c =>
      exact ⟨C c, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨P₁, r₁, hr₁, h₁⟩ := hx
      obtain ⟨P₂, r₂, hr₂, h₂⟩ := hy
      exact ⟨P₁ + P₂, r₁ + r₂, add_mem hr₁ hr₂, by rw [h₁, h₂, map_add]; ring⟩
  | mul x y hx' hy' hx hy =>
      obtain ⟨P₁, r₁, hr₁, h₁⟩ := hx
      obtain ⟨P₂, r₂, hr₂, h₂⟩ := hy
      have hΘ : ι (θ : F₀) ∈ Rv K F v := coe_mem_Rv v θ
      have hPi : ι (π : F₀) ∈ Rv K F v := coe_mem_Rv v π
      refine ⟨P₁ * P₂, r₁ * aeval (ι (θ : F₀)) P₂ + aeval (ι (θ : F₀)) P₁ * r₂
        + ι (π : F₀) * r₁ * r₂, ?_, ?_⟩
      · exact add_mem (add_mem (mul_mem hr₁ (aeval_mem_Rv v hΘ P₂))
          (mul_mem (aeval_mem_Rv v hΘ P₁) hr₂)) (mul_mem (mul_mem hPi hr₁) hr₂)
      · rw [h₁, h₂, map_mul]; ring

theorem exists_div (v : Place k F₀)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) (x : F) :
    ∃ r ∈ Rv K F v, ∃ s ∈ Rv K F v, s ≠ 0 ∧ x = r / s := by
  have hle : IntermediateField.adjoin K (Set.range (algebraMap F₀ F))
      ≤ IntermediateField.adjoin K (algebraMap F₀ F '' (v.toValuationSubring : Set F₀)) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    rcases v.toValuationSubring.mem_or_inv_mem f with hf | hf
    · exact IntermediateField.subset_adjoin _ _ ⟨f, hf, rfl⟩
    · have : ι f = (ι f⁻¹)⁻¹ := by simp
      rw [this]
      exact inv_mem (IntermediateField.subset_adjoin _ _ ⟨_, hf, rfl⟩)
  have hx : x ∈ IntermediateField.adjoin K
      (algebraMap F₀ F '' (v.toValuationSubring : Set F₀)) := by
    apply hle
    rw [hgen]
    trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hx
  obtain ⟨r, hr, s, hs, rfl⟩ := hx
  by_cases hs0 : s = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [hs0]⟩
  · exact ⟨r, hr, s, hs, hs0, rfl⟩

theorem exists_sum_of_mem_Rv (v : Place k F₀) {r : F} (hr : r ∈ Rv K F v) :
    ∃ n : ℕ, ∃ c : Fin n → K, ∃ f : Fin n → F₀,
      (∀ i, f i ∈ v.toValuationSubring) ∧ r = ∑ i, c i • ι (f i) := by
  set sO : Set F := algebraMap F₀ F '' (v.toValuationSubring : Set F₀) with hsO
  let M : Submonoid F := (v.toValuationSubring.toSubring.toSubmonoid).map (algebraMap F₀ F : F₀ →* F)
  have hM : (M : Set F) = sO := Submonoid.coe_map _ _
  have hcl : Submonoid.closure sO = M :=
    Submonoid.closure_eq_of_le (hM ▸ subset_rfl) (hM ▸ Submonoid.subset_closure)
  have hspan : Subalgebra.toSubmodule (Rv K F v) = Submodule.span K sO := by
    rw [Rv, Algebra.adjoin_eq_span, ← hsO, hcl, hM]
  have hr' : r ∈ Submodule.span K sO := by
    rw [← hspan]; exact hr
  rw [Submodule.mem_span_set'] at hr'
  obtain ⟨n, c, g, hsum⟩ := hr'
  have hg : ∀ i, ∃ f : F₀, f ∈ v.toValuationSubring ∧ ι f = (g i : F) := fun i => (g i).2
  choose f hf hfι using hg
  exact ⟨n, c, f, hf, by rw [← hsum]; simp [hfι]⟩

end RingR

section AlphaW

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

local notation "ι" => algebraMap F₀ F

theorem theta_mem {v : Place k F₀} {W : Place K F} (hW : Over v W) (θ : v.toValuationSubring) :
    ι (θ : F₀) ∈ W.toValuationSubring :=
  (mem_iff_of_over hW _).mp θ.2

def αv {v : Place k F₀} (W : Place K F) (hb : ResBij W) (hW : Over v W)
    (θ : v.toValuationSubring) : K :=
  resHom W hb ⟨ι (θ : F₀), theta_mem hW θ⟩

theorem theta_sub_alpha_mem {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    (θ : v.toValuationSubring) :
    ι (θ : F₀) - algebraMap K F (αv W hb hW θ) ∈ W.toValuationSubring.nonunits := by
  unfold αv; exact resHom_spec W hb ⟨_, theta_mem hW θ⟩

theorem alpha_eq_of_mem_nonunits {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    (θ : v.toValuationSubring) {a : K}
    (h : ι (θ : F₀) - algebraMap K F a ∈ W.toValuationSubring.nonunits) : αv W hb hW θ = a := by
  unfold αv; exact (resHom_eq_iff W hb ⟨_, theta_mem hW θ⟩ a).mpr h

theorem coe_mem_nonunits_iff {v : Place k F₀} (x : v.toValuationSubring) :
    (x : F₀) ∈ v.toValuationSubring.nonunits ↔ x ∈ maximalIdeal v.toValuationSubring := by
  rw [← mk_mem_maximalIdeal_iff_mem_nonunits v.toValuationSubring x.2]

theorem pi_mem_nonunits {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    ι (π : F₀) ∈ W.toValuationSubring.nonunits := by
  rw [nonunits_iff_of_over hW, coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal]
  exact hπ.not_isUnit

theorem pi_ne_zero {v : Place k F₀} {π : v.toValuationSubring} (hπ : Irreducible π) :
    ι (π : F₀) ≠ 0 := by
  rw [map_ne_zero_iff _ (algebraMap F₀ F).injective]
  exact_mod_cast hπ.ne_zero

theorem mem_nonunits_iff_isRoot {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) {r r' : F} (hr' : r' ∈ Rv K F v)
    {P : K[X]} (hr : r = aeval (ι (θ : F₀)) P + ι (π : F₀) * r') :
    r ∈ W.toValuationSubring.nonunits ↔ P.IsRoot (αv W hb hW θ) := by
  have hΘ := theta_mem hW θ
  have hr'W : r' ∈ W.toValuationSubring := Rv_le_of_over hW hr'
  have hPiu := pi_mem_nonunits (K := K) (F := F) hW hπ
  have hPiW : ι (π : F₀) ∈ W.toValuationSubring := nonunits_le _ hPiu
  have hrW : r ∈ W.toValuationSubring := by
    rw [hr]; exact add_mem (aeval_mem W hΘ P) (mul_mem hPiW hr'W)
  rw [show (r ∈ W.toValuationSubring.nonunits)
      = (((⟨r, hrW⟩ : W.toValuationSubring) : F) ∈ W.toValuationSubring.nonunits) from rfl,
    mem_nonunits_iff_resHom_eq_zero W hb]
  have hdec : (⟨r, hrW⟩ : W.toValuationSubring)
      = ⟨aeval (ι (θ : F₀)) P, aeval_mem W hΘ P⟩ + ⟨ι (π : F₀), hPiW⟩ * ⟨r', hr'W⟩ := by
    apply Subtype.ext
    simp [hr]
  have hPi0 : resHom W hb ⟨ι (π : F₀), hPiW⟩ = 0 :=
    (mem_nonunits_iff_resHom_eq_zero W hb _).mp hPiu
  rw [hdec, map_add, map_mul, hPi0, zero_mul, add_zero, resHom_aeval]
  rfl

theorem isRoot_alpha {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) :
    ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).IsRoot (αv W hb hW θ) := by
  obtain ⟨g, hg⟩ := exists_aeval_minpoly_eq v hπ (θ := θ)
  have hPiu := pi_mem_nonunits (K := K) (F := F) hW hπ
  have heq : aeval (ι (θ : F₀)) ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
      = aeval (ι (θ : F₀)) ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
        + ι (π : F₀) * 0 := by ring
  rw [← mem_nonunits_iff_isRoot hb hW hπ (zero_mem _) heq, ← algebraMap_coe_aeval, hg]
  push_cast
  rw [mul_comm]
  exact mul_mem_nonunits _ (Rv_le_of_over hW (coe_mem_Rv v g)) hPiu

theorem not_isRoot_divByMonic {p : K[X]} (hsep : p.Separable) {a : K} (ha : p.IsRoot a) :
    ¬ (p /ₘ (X - C a)).IsRoot a := by
  intro h
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h
  have hp : p = (X - C a) * ((X - C a) * q) := by
    rw [← hq]; exact (mul_divByMonic_eq_iff_isRoot.mpr ha).symm
  have hdvd : (X - C a) * (X - C a) ∣ p := ⟨q, by rw [hp]; ring⟩
  exact not_isUnit_X_sub_C a (hsep.squarefree _ hdvd)

theorem e_notMem_nonunits {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    aeval (ι (θ : F₀)) (((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
      /ₘ (X - C (αv W hb hW θ))) ∉ W.toValuationSubring.nonunits := by
  set q := ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)) /ₘ (X - C (αv W hb hW θ))
  have heq : aeval (ι (θ : F₀)) q = aeval (ι (θ : F₀)) q + ι (π : F₀) * 0 := by ring
  rw [mem_nonunits_iff_isRoot hb hW hπ (zero_mem _) heq]
  exact not_isRoot_divByMonic hsep (isRoot_alpha hb hW hπ)

theorem e_mul_eq {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hb : ResBij W) (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    {r : F} (hr : r ∈ Rv K F v) (hru : r ∈ W.toValuationSubring.nonunits) :
    ∃ r₂ ∈ Rv K F v,
      aeval (ι (θ : F₀)) (((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
        /ₘ (X - C (αv W hb hW θ))) * r = ι (π : F₀) * r₂ := by
  set μK := (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) with hμK
  set α := αv W hb hW θ with hα
  set q := μK /ₘ (X - C α) with hq
  obtain ⟨P, r', hr', hrP⟩ := exists_decomp v hπ hθ hr
  have hroot : P.IsRoot α := (mem_nonunits_iff_isRoot hb hW hπ hr' hrP).mp hru
  have hP : (X - C α) * (P /ₘ (X - C α)) = P := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hμ : (X - C α) * q = μK := mul_divByMonic_eq_iff_isRoot.mpr (isRoot_alpha hb hW hπ)
  obtain ⟨g, hg⟩ := exists_aeval_minpoly_eq v hπ (θ := θ)
  have haeμ : aeval (ι (θ : F₀)) μK = ι (π : F₀) * ι (g : F₀) := by
    rw [hμK, ← algebraMap_coe_aeval, hg]; push_cast; ring
  have hΘ : ι (θ : F₀) ∈ Rv K F v := coe_mem_Rv v θ
  refine ⟨ι (g : F₀) * aeval (ι (θ : F₀)) (P /ₘ (X - C α)) + aeval (ι (θ : F₀)) q * r', ?_, ?_⟩
  · exact add_mem (mul_mem (coe_mem_Rv v g) (aeval_mem_Rv v hΘ _))
      (mul_mem (aeval_mem_Rv v hΘ _) hr')
  · have key : aeval (ι (θ : F₀)) q * aeval (ι (θ : F₀)) P
        = ι (π : F₀) * (ι (g : F₀) * aeval (ι (θ : F₀)) (P /ₘ (X - C α))) := by
      conv_lhs => rw [← hP]
      rw [← map_mul, ← mul_assoc, mul_comm q, hμ, map_mul, haeμ, mul_assoc]
    rw [hrP, mul_add, key]
    ring

end AlphaW

section Uniqueness

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

local notation "ι" => algebraMap F₀ F

theorem one_notMem_nonunits {L : Type*} [Field L] (B : ValuationSubring L) :
    (1 : L) ∉ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_one]; exact lt_irrefl 1

theorem ord_pos_of_mem_nonunits (W : Place K F) {x : F} (hx : x ∈ W.toValuationSubring.nonunits)
    (hx0 : x ≠ 0) : 0 < W.ord x := by
  have h := (mk_mem_maximalIdeal_iff_mem_nonunits W.toValuationSubring (nonunits_le _ hx)).mpr hx
  rw [Place.mk_mem_maximalIdeal_iff] at h
  exact h.resolve_left hx0

theorem ord_eq_zero_of_notMem_nonunits (W : Place K F) {x : F} (hxW : x ∈ W.toValuationSubring)
    (hx : x ∉ W.toValuationSubring.nonunits) : W.ord x = 0 := by
  obtain ⟨u, hu⟩ := isUnit_mk_of_notMem_nonunits _ hxW hx
  have : x = ((u : W.toValuationSubring) : F) := by rw [hu]
  rw [this]
  exact W.ord_coe_unit u

theorem exists_factor {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hb : ResBij W) (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable)
    {r : F} (hr : r ∈ Rv K F v) (hr0 : r ≠ 0) :
    ∃ n : ℕ, ∃ s ∈ Rv K F v, ∃ u ∈ Rv K F v, s ∉ W.toValuationSubring.nonunits ∧
      u ∉ W.toValuationSubring.nonunits ∧ s * r = ι (π : F₀) ^ n * u := by
  set e := aeval (ι (θ : F₀)) (((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
        /ₘ (X - C (αv W hb hW θ))) with he
  have heR : e ∈ Rv K F v := aeval_mem_Rv v (coe_mem_Rv v θ) _
  have heu : e ∉ W.toValuationSubring.nonunits := e_notMem_nonunits hb hW hπ hsep
  have heW : e ∈ W.toValuationSubring := Rv_le_of_over hW heR
  have he0 : e ≠ 0 := ne_zero_of_notMem_nonunits _ heu
  have hPiu := pi_mem_nonunits (K := K) (F := F) hW hπ
  have hPi0 : ι (π : F₀) ≠ 0 := pi_ne_zero hπ
  have hPipos : 0 < W.ord (ι (π : F₀)) := ord_pos_of_mem_nonunits W hPiu hPi0
  suffices H : ∀ m : ℕ, ∀ r ∈ Rv K F v, r ≠ 0 → (W.ord r).toNat = m →
      ∃ n : ℕ, ∃ s ∈ Rv K F v, ∃ u ∈ Rv K F v, s ∉ W.toValuationSubring.nonunits ∧
        u ∉ W.toValuationSubring.nonunits ∧ s * r = ι (π : F₀) ^ n * u from H _ r hr hr0 rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro r hr hr0 hm
    by_cases hru : r ∈ W.toValuationSubring.nonunits
    · obtain ⟨r₂, hr₂, her⟩ := e_mul_eq hb hW hπ hθ hr hru
      have hr₂0 : r₂ ≠ 0 := by
        rintro rfl
        rw [mul_zero, mul_eq_zero] at her
        exact her.elim he0 hr0
      have hr₂W : r₂ ∈ W.toValuationSubring := Rv_le_of_over hW hr₂
      have hord : W.ord r = W.ord (ι (π : F₀)) + W.ord r₂ := by
        have h1 := W.ord_mul he0 hr0
        rw [her, W.ord_mul hPi0 hr₂0, ord_eq_zero_of_notMem_nonunits W heW heu, zero_add] at h1
        exact h1.symm
      have hrpos : 0 < W.ord r := ord_pos_of_mem_nonunits W hru hr0
      have hr₂nn : 0 ≤ W.ord r₂ := (Place.mem_iff_ord_nonneg W hr₂0).mp hr₂W
      have hlt : (W.ord r₂).toNat < m := by
        rw [← hm, Int.toNat_lt_toNat hrpos]
        omega
      obtain ⟨n, s, hs, u, hu, hsu, huu, hfac⟩ := ih _ hlt r₂ hr₂ hr₂0 rfl
      refine ⟨n + 1, s * e, mul_mem hs heR, u, hu,
        mul_notMem_nonunits _ (Rv_le_of_over hW hs) heW hsu heu, huu, ?_⟩
      calc s * e * r = s * (e * r) := by ring
        _ = s * (ι (π : F₀) * r₂) := by rw [her]
        _ = ι (π : F₀) * (s * r₂) := by ring
        _ = ι (π : F₀) * (ι (π : F₀) ^ n * u) := by rw [hfac]
        _ = ι (π : F₀) ^ (n + 1) * u := by ring
    · exact ⟨0, 1, one_mem _, r, hr, one_notMem_nonunits _, hru, by simp⟩

theorem div_mem_iff_of_factor {L : Type*} [Field L] (B : ValuationSubring L)
    {ϖ r s sr ur ss us : L} (hϖ : ϖ ∈ B.nonunits) (hϖ0 : ϖ ≠ 0)
    (hsrB : sr ∈ B) (hurB : ur ∈ B) (hssB : ss ∈ B) (husB : us ∈ B)
    (hsr : sr ∉ B.nonunits) (hur : ur ∉ B.nonunits) (hss : ss ∉ B.nonunits)
    (hus : us ∉ B.nonunits) (hs0 : s ≠ 0) {a b : ℕ}
    (hfr : sr * r = ϖ ^ a * ur) (hfs : ss * s = ϖ ^ b * us) :
    r / s ∈ B ↔ b ≤ a := by
  set γ := B.valuation ϖ with hγ
  have hγ0 : 0 < γ := by
    rw [hγ, zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hϖ0
  have hγ1 : γ < 1 := (ValuationSubring.mem_nonunits_iff _).mp hϖ
  have hvr : B.valuation r = γ ^ a := by
    have := congrArg B.valuation hfr
    rw [map_mul, map_mul, map_pow, valuation_eq_one_of_notMem_nonunits B hsrB hsr,
      valuation_eq_one_of_notMem_nonunits B hurB hur, one_mul, mul_one] at this
    exact this
  have hvs : B.valuation s = γ ^ b := by
    have := congrArg B.valuation hfs
    rw [map_mul, map_mul, map_pow, valuation_eq_one_of_notMem_nonunits B hssB hss,
      valuation_eq_one_of_notMem_nonunits B husB hus, one_mul, mul_one] at this
    exact this
  have hvs0 : 0 < B.valuation s := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hs0
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ hvs0, hvr, hvs]
  exact pow_le_pow_iff_right_of_lt_one₀ hγ0 hγ1

theorem nonunits_iff_of_alpha_eq {v : Place k F₀} [Module.Finite k v.ResidueField]
    {W₁ W₂ : Place K F} (hb₁ : ResBij W₁) (hb₂ : ResBij W₂) (hW₁ : Over v W₁) (hW₂ : Over v W₂)
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hα : αv W₁ hb₁ hW₁ θ = αv W₂ hb₂ hW₂ θ) {r : F} (hr : r ∈ Rv K F v) :
    r ∈ W₁.toValuationSubring.nonunits ↔ r ∈ W₂.toValuationSubring.nonunits := by
  obtain ⟨P, r', hr', hrP⟩ := exists_decomp v hπ hθ hr
  rw [mem_nonunits_iff_isRoot hb₁ hW₁ hπ hr' hrP, mem_nonunits_iff_isRoot hb₂ hW₂ hπ hr' hrP, hα]

theorem eq_of_alpha_eq {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W₁ W₂ : Place K F} (hb₁ : ResBij W₁) (hb₂ : ResBij W₂) (hW₁ : Over v W₁) (hW₂ : Over v W₂)
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable)
    (hα : αv W₁ hb₁ hW₁ θ = αv W₂ hb₂ hW₂ θ) : W₁ = W₂ := by
  have hPi0 : ι (π : F₀) ≠ 0 := pi_ne_zero hπ
  have hPi₁ := pi_mem_nonunits (K := K) (F := F) hW₁ hπ
  have hPi₂ := pi_mem_nonunits (K := K) (F := F) hW₂ hπ
  have tr : ∀ {x : F}, x ∈ Rv K F v → x ∉ W₁.toValuationSubring.nonunits →
      x ∉ W₂.toValuationSubring.nonunits := fun hx h₁ h₂ =>
    h₁ ((nonunits_iff_of_alpha_eq hb₁ hb₂ hW₁ hW₂ hπ hθ hα hx).mpr h₂)
  apply Place.ext
  ext x
  obtain ⟨r, hr, s, hs, hs0, rfl⟩ := exists_div v hgen x
  by_cases hr0 : r = 0
  · simp [hr0]
  obtain ⟨a, sr, hsr, ur, hur, hsr₁, hur₁, hfr⟩ := exists_factor hb₁ hW₁ hπ hθ hsep hr hr0
  obtain ⟨b, ss, hss, us, hus, hss₁, hus₁, hfs⟩ := exists_factor hb₁ hW₁ hπ hθ hsep hs hs0
  rw [div_mem_iff_of_factor W₁.toValuationSubring hPi₁ hPi0 (Rv_le_of_over hW₁ hsr)
      (Rv_le_of_over hW₁ hur) (Rv_le_of_over hW₁ hss) (Rv_le_of_over hW₁ hus)
      hsr₁ hur₁ hss₁ hus₁ hs0 hfr hfs,
    div_mem_iff_of_factor W₂.toValuationSubring hPi₂ hPi0 (Rv_le_of_over hW₂ hsr)
      (Rv_le_of_over hW₂ hur) (Rv_le_of_over hW₂ hss) (Rv_le_of_over hW₂ hus)
      (tr hsr hsr₁) (tr hur hur₁) (tr hss hss₁) (tr hus hus₁) hs0 hfr hfs]

end Uniqueness

section Existence

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

local notation "ι" => algebraMap F₀ F

theorem eq_of_le_of_ne_top (v : Place k F₀) {O' : ValuationSubring F₀}
    (hle : v.toValuationSubring ≤ O') (hne : O' ≠ ⊤) : O' = v.toValuationSubring := by
  by_contra hne'
  have hlt : v.toValuationSubring < O' := lt_of_le_of_ne hle (Ne.symm hne')
  obtain ⟨x, hxO', hxv⟩ := SetLike.exists_of_lt hlt
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hϖ0 : (ϖ : F₀) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ zero_mem _)
  have hxinv : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hxv
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow (inv_ne_zero hx0) hϖ
  set n := v.ord x⁻¹ with hn
  have hn0 : 0 ≤ n := (Place.mem_iff_ord_nonneg v (inv_ne_zero hx0)).mp hxinv
  have hn1 : n ≠ 0 := by
    intro hzero
    rw [hzero, zpow_zero, mul_one] at hu
    apply hxv
    have hxu : x = (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F₀) := by
      rw [← inv_inv x, hu]
      symm
      apply eq_inv_of_mul_eq_one_right
      have h := congrArg Subtype.val (Units.mul_inv u)
      rw [Subring.coe_mul] at h
      exact h
    rw [hxu]
    exact Subtype.mem _
  have hϖO' : (ϖ : F₀) ∈ O' := hle ϖ.2
  have hϖinv : (ϖ : F₀)⁻¹ ∈ O' := by
    have hxu : x * (u : F₀) * (ϖ : F₀) ^ n = 1 := by
      rw [mul_assoc, ← hu, mul_inv_cancel₀ hx0]
    have : (ϖ : F₀)⁻¹ = x * (u : F₀) * (ϖ : F₀) ^ (n - 1) := by
      rw [zpow_sub_one₀ hϖ0, ← mul_assoc, hxu, one_mul]
    rw [this]
    refine mul_mem (mul_mem hxO' (hle u.1.2)) ?_
    have hpow : (ϖ : F₀) ^ (n - 1) = (ϖ : F₀) ^ ((n - 1).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hpow]
    exact pow_mem hϖO' _
  have hϖunit : (ϖ : F₀) ∉ O'.nonunits := fun h => inv_notMem_of_mem_nonunits O' hϖ0 h hϖinv
  have hval : O'.valuation (ϖ : F₀) = 1 := valuation_eq_one_of_notMem_nonunits O' hϖO' hϖunit
  apply hne
  ext y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  obtain ⟨u', hu'⟩ := v.exists_unit_mul_zpow hy0 hϖ
  rw [hu']
  refine mul_mem (hle u'.1.2) ?_
  rw [← O'.valuation_le_one_iff, map_zpow₀, hval, one_zpow]

def Nsub (v : Place k F₀) : Submodule k F₀ where
  carrier := {y | v.toValuationSubring.valuation y < 1}
  zero_mem' := by
    change v.toValuationSubring.valuation 0 < 1
    rw [map_zero]; exact zero_lt_one
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    exact lt_of_le_of_lt (Valuation.map_add _ x y) (max_lt hx hy)
  smul_mem' := by
    intro c y hy
    change v.toValuationSubring.valuation (c • y) < 1
    have hc : v.toValuationSubring.valuation (algebraMap k F₀ c) ≤ 1 :=
      (v.toValuationSubring.valuation_le_one_iff _).mpr (v.algebraMap_mem' c)
    rw [Algebra.smul_def, map_mul]
    calc v.toValuationSubring.valuation (algebraMap k F₀ c) * v.toValuationSubring.valuation y
        ≤ 1 * v.toValuationSubring.valuation y := mul_le_mul_left hc _
      _ = v.toValuationSubring.valuation y := one_mul _
      _ < 1 := hy

theorem mem_Nsub (v : Place k F₀) (y : F₀) : y ∈ Nsub v ↔ v.toValuationSubring.valuation y < 1 :=
  Iff.rfl

theorem linearIndependent_pow_theta (v : Place k F₀) (θ : v.toValuationSubring) :
    LinearIndependent k
      (fun i : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree => (θ : F₀) ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  apply coeff_eq_zero_of_sum_smul_pow_mem v θ a
  rw [ha, map_zero]
  exact zero_lt_one

theorem disjoint_span_pow_Nsub (v : Place k F₀) (θ : v.toValuationSubring) :
    Disjoint (Submodule.span k (Set.range
      (fun i : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree => (θ : F₀) ^ (i : ℕ))))
      (Nsub v) := by
  rw [Submodule.disjoint_def]
  intro x hx hN
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
  have := coeff_eq_zero_of_sum_smul_pow_mem v θ a hN
  simp [this]

theorem algebraMap_mem_span_image {t : Set F₀} {z : F₀} (hz : z ∈ Submodule.span k t) :
    ι z ∈ Submodule.span K (algebraMap F₀ F '' t) := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
      have : ι (c • x) = algebraMap k K c • ι x := by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this]
      exact Submodule.smul_mem _ _ hx

theorem coeff_eq_zero_of_LD
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (v : Place k F₀) (θ : v.toValuationSubring)
    (a : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree → K) {y : F}
    (hy : y ∈ Submodule.span K (algebraMap F₀ F '' (Nsub v : Set F₀)))
    (h : ∑ i, a i • ι (θ : F₀) ^ (i : ℕ) = y) : ∀ i, a i = 0 := by
  classical
  rw [Submodule.mem_span_set'] at hy
  obtain ⟨n, c, g, rfl⟩ := hy
  have hg : ∀ j, ∃ f : F₀, f ∈ (Nsub v : Set F₀) ∧ ι f = (g j : F) := fun j => (g j).2
  choose f hfN hfι using hg
  obtain ⟨b, hbt, hspan, hbind⟩ := exists_linearIndependent k (Set.range f)
  have hbfin : b.Finite := (Set.finite_range f).subset hbt
  letI : Fintype b := hbfin.fintype
  have hrange : Set.range (fun z : b => ι (z : F₀)) = algebraMap F₀ F '' b := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]
  have hy' : (∑ j, c j • (g j : F)) ∈ Submodule.span K (Set.range fun z : b => ι (z : F₀)) := by
    rw [hrange]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    rw [← hfι j]
    apply algebraMap_mem_span_image (k := k)
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
  let w : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree ⊕ b → F₀ :=
    Sum.elim (fun i => (θ : F₀) ^ (i : ℕ)) (fun z => (z : F₀))
  have hw : LinearIndependent k w := by
    apply LinearIndependent.sum_type (linearIndependent_pow_theta v θ) hbind
    refine (disjoint_span_pow_Nsub v θ).mono_right ?_
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hfN j
  let coef : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree ⊕ b → K :=
    Sum.elim a (fun z => - c' z)
  have hrel : ∑ x, algebraMap K F (coef x) * ι (w x) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [w, coef, Sum.elim_inl, Sum.elim_inr, map_pow, map_neg, neg_mul,
      Finset.sum_neg_distrib]
    have e1 : ∑ i : Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree,
        algebraMap K F (a i) * ι (θ : F₀) ^ (i : ℕ) = ∑ i, a i • ι (θ : F₀) ^ (i : ℕ) := by
      simp [Algebra.smul_def]
    have e2 : ∑ z : b, algebraMap K F (c' z) * ι (z : F₀) = ∑ z : b, c' z • ι (z : F₀) := by
      simp [Algebra.smul_def]
    rw [e1, e2, h, hc', add_neg_cancel]
  let e := (Fintype.equivFin (Fin (minpoly k (IsLocalRing.residue _ θ)).natDegree ⊕ b)).symm
  have hsum : ∑ i, algebraMap K F ((coef ∘ e) i) * ι ((w ∘ e) i) = 0 := by
    rw [show ∑ i, algebraMap K F ((coef ∘ e) i) * ι ((w ∘ e) i)
        = ∑ x, algebraMap K F (coef x) * ι (w x) from
      Equiv.sum_comp e (fun x => algebraMap K F (coef x) * ι (w x))]
    exact hrel
  have hLD' := hLD _ (w ∘ e) (coef ∘ e) (hw.comp e e.injective) hsum
  intro i
  have := hLD' (e.symm (Sum.inl i))
  simpa [coef] using this

theorem valuation_pi_lt_one (v : Place k F₀) {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.toValuationSubring.valuation (π : F₀) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal]
  exact hπ.not_isUnit

theorem aeval_divByMonic_ne
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (v : Place k F₀) [Module.Finite k v.ResidueField] {θ π : v.toValuationSubring}
    (hπ : Irreducible π) {α : K}
    (hα : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).IsRoot α)
    {r₀ : F} (hr₀ : r₀ ∈ Rv K F v) :
    aeval (ι (θ : F₀)) (((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
      /ₘ (X - C α)) ≠ ι (π : F₀) * r₀ := by
  intro heq
  set μ := minpoly k (IsLocalRing.residue _ θ) with hμ
  set q := (μ.map (algebraMap k K)) /ₘ (X - C α) with hq
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  have hμK0 : μ.map (algebraMap k K) ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hμq : (X - C α) * q = μ.map (algebraMap k K) := mul_divByMonic_eq_iff_isRoot.mpr hα
  have hq0 : q ≠ 0 := by
    intro h; rw [h, mul_zero] at hμq; exact hμK0 hμq.symm
  set d := μ.natDegree with hd
  have hdpos : 0 < d := minpoly.natDegree_pos hint
  have hqdeg : q.natDegree < d := by
    rw [hq, natDegree_divByMonic _ (monic_X_sub_C α), natDegree_map, natDegree_X_sub_C]
    omega

  obtain ⟨n, c, f, hf, hr₀eq⟩ := exists_sum_of_mem_Rv v hr₀
  have hy : ι (π : F₀) * r₀ ∈ Submodule.span K (algebraMap F₀ F '' (Nsub v : Set F₀)) := by
    rw [hr₀eq, Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mul_smul_comm, ← map_mul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(π : F₀) * f j, ?_, rfl⟩)
    change v.toValuationSubring.valuation ((π : F₀) * f j) < 1
    rw [mul_comm, ← ValuationSubring.mem_nonunits_iff]
    exact mul_mem_nonunits _ (hf j)
      ((ValuationSubring.mem_nonunits_iff _).mpr (valuation_pi_lt_one v hπ))

  have hsum : aeval (ι (θ : F₀)) q = ∑ i : Fin d, q.coeff i • ι (θ : F₀) ^ (i : ℕ) := by
    rw [aeval_eq_sum_range' hqdeg, Finset.sum_range (fun i => q.coeff i • ι (θ : F₀) ^ i)]
  have hzero := coeff_eq_zero_of_LD hLD v θ (fun i => q.coeff i) hy (by rw [← hsum]; exact heq)
  apply hq0
  ext m
  rw [coeff_zero]
  by_cases hm : m < d
  · exact hzero ⟨m, hm⟩
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hqdeg (not_lt.mp hm))

theorem exists_place_of_isRoot
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (hsepx : ∃ x : F, FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    (hb : ∀ W : Place K F, ResBij W)
    (v : Place k F₀) [Module.Finite k v.ResidueField] {θ π : v.toValuationSubring}
    (hπ : Irreducible π) {α : K}
    (hα : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).IsRoot α) :
    ∃ W : Place K F, ∃ hW : Over v W, αv W (hb W) hW θ = α := by
  classical
  set μK := (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) with hμK
  let A : Subring F := (Rv K F v).toSubring
  have hPiA : ι (π : F₀) ∈ A := coe_mem_Rv v π
  have hΘA : ι (θ : F₀) - algebraMap K F α ∈ A :=
    sub_mem (coe_mem_Rv v θ) (algebraMap_mem (Rv K F v) α)
  let I : Ideal A := Ideal.span {⟨ι (π : F₀), hPiA⟩, ⟨ι (θ : F₀) - algebraMap K F α, hΘA⟩}

  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1
    have hab' : (a : F) * ι (π : F₀) + (b : F) * (ι (θ : F₀) - algebraMap K F α) = 1 := by
      have := congrArg Subtype.val hab
      simpa using this
    set q := μK /ₘ (X - C α) with hq
    have hμ : (X - C α) * q = μK := mul_divByMonic_eq_iff_isRoot.mpr hα
    obtain ⟨g, hg⟩ := exists_aeval_minpoly_eq v hπ (θ := θ)
    have haeμ : aeval (ι (θ : F₀)) μK = ι (π : F₀) * ι (g : F₀) := by
      rw [hμK, ← algebraMap_coe_aeval, hg]; push_cast; ring
    have hΘα : aeval (ι (θ : F₀)) q * (ι (θ : F₀) - algebraMap K F α)
        = ι (π : F₀) * ι (g : F₀) := by
      rw [show ι (θ : F₀) - algebraMap K F α = aeval (ι (θ : F₀)) (X - C α) by simp, ← map_mul,
        mul_comm q, hμ, haeμ]
    have key : aeval (ι (θ : F₀)) q
        = ι (π : F₀) * (aeval (ι (θ : F₀)) q * a + b * ι (g : F₀)) := by
      calc aeval (ι (θ : F₀)) q
          = aeval (ι (θ : F₀)) q * ((a : F) * ι (π : F₀)
              + (b : F) * (ι (θ : F₀) - algebraMap K F α)) := by rw [hab', mul_one]
        _ = ι (π : F₀) * (aeval (ι (θ : F₀)) q * a)
              + b * (aeval (ι (θ : F₀)) q * (ι (θ : F₀) - algebraMap K F α)) := by ring
        _ = ι (π : F₀) * (aeval (ι (θ : F₀)) q * a + b * ι (g : F₀)) := by rw [hΘα]; ring
    refine aeval_divByMonic_ne hLD v hπ hα ?_ key
    exact add_mem (mul_mem (aeval_mem_Rv v (coe_mem_Rv v θ) _) a.2)
      (mul_mem b.2 (coe_mem_Rv v g))

  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hPiB : ι (π : F₀) ∈ B.nonunits :=
    hIB ⟨⟨ι (π : F₀), hPiA⟩, Ideal.subset_span (by simp), rfl⟩
  have hΘB : ι (θ : F₀) - algebraMap K F α ∈ B.nonunits :=
    hIB ⟨⟨_, hΘA⟩, Ideal.subset_span (by simp), rfl⟩
  have hKB : ∀ c : K, algebraMap K F c ∈ B := fun c =>
    hAB (show algebraMap K F c ∈ A from algebraMap_mem (Rv K F v) c)
  have hPiinv : (ι (π : F₀))⁻¹ ∉ B := inv_notMem_of_mem_nonunits B (pi_ne_zero hπ) hPiB

  obtain ⟨x, hfd, hsx⟩ := hsepx
  haveI := hfd
  haveI := hsx
  obtain ⟨W, hWB⟩ := Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable x
    (RingHom.id F) B (fun c => hKB c) ⟨_, hPiinv⟩
  have hWB' : W.toValuationSubring = B := by
    rw [hWB]; ext y; simp [ValuationSubring.mem_comap]

  have hW : Over v W := by
    unfold Over
    apply eq_of_le_of_ne_top v
    · intro f hf
      rw [ValuationSubring.mem_comap, hWB']
      exact hAB (show ι f ∈ A from algebraMap_mem_Rv v hf)
    · intro htop
      have : (π : F₀)⁻¹ ∈ W.toValuationSubring.comap (algebraMap F₀ F) := htop ▸ trivial
      rw [ValuationSubring.mem_comap, map_inv₀, hWB'] at this
      exact hPiinv this
  refine ⟨W, hW, alpha_eq_of_mem_nonunits (hb W) hW θ ?_⟩
  rw [hWB']
  exact hΘB

end Existence

section EssFinite

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem essFiniteType_of_gen (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.EssFiniteType K F := by
  classical
  obtain ⟨s, hs⟩ := hfg
  rw [← IntermediateField.fg_top_iff]
  refine ⟨s.image (algebraMap F₀ F), ?_⟩
  rw [Finset.coe_image, eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨f, rfl⟩
  have hf : f ∈ IntermediateField.adjoin k (s : Set F₀) := by rw [hs]; trivial
  have h1 : (IsScalarTower.toAlgHom k F₀ F) f ∈
      (IntermediateField.adjoin k (s : Set F₀)).map (IsScalarTower.toAlgHom k F₀ F) := ⟨f, hf, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin k (⇑(IsScalarTower.toAlgHom k F₀ F) '' (s : Set F₀))
      ≤ (IntermediateField.adjoin K (algebraMap F₀ F '' (s : Set F₀))).restrictScalars k := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    exact IntermediateField.subset_adjoin K _ hy
  exact h2 h1

end EssFinite

end CFEFibre
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.AlgebraicCurve.CFEFibre"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.AlgebraicCurve.CFEFibre P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint.AlgebraicCurve AlgebraicCurve.CFEFibre Polynomial in
theorem solution
    {k K F₀ F : Type*} [Field k] [PerfectField k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (v : AlgebraicCurve.Place k F₀) :
    {W : AlgebraicCurve.Place K F |
        W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring}.Finite ∧
    Nat.card {W : AlgebraicCurve.Place K F |
        W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring} = v.deg ∧
    ∀ W₁ W₂ : AlgebraicCurve.Place K F,
      W₁.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring →
      W₂.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring →
      (∀ f : F₀, f ∈ v.toValuationSubring → ∀ a : K,
        algebraMap F₀ F f - algebraMap K F a ∈ W₁.toValuationSubring.nonunits →
        algebraMap F₀ F f - algebraMap K F a ∈ W₂.toValuationSubring.nonunits) →
      W₁ = W₂ := by
  classical

  haveI : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsAlgebraic k v.ResidueField := Algebra.IsAlgebraic.of_finite k _
  haveI : Algebra.IsSeparable k v.ResidueField := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨θb, hθb⟩ := Field.exists_primitive_element k v.ResidueField
  obtain ⟨θ, rfl⟩ := IsLocalRing.residue_surjective θb
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  have hμsep : (minpoly k (IsLocalRing.residue _ θ)).Separable :=
    Algebra.IsSeparable.isSeparable k _
  have hμKsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable :=
    hμsep.map
  have hd : (minpoly k (IsLocalRing.residue _ θ)).natDegree = v.deg :=
    natDegree_minpoly_eq_deg v hθb
  have hb : ∀ W : Place K F, ResBij W := resBij_of_isAlgClosed
  haveI : Algebra.EssFiniteType K F := essFiniteType_of_gen hfg hgen
  have hsepx : ∃ x : F, FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F := by
    obtain ⟨t, -, h1, h2⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
    exact ⟨t, h1, h2⟩

  set S := (minpoly k (IsLocalRing.residue _ θ)).rootSet K with hS
  have hmemS : ∀ a : K, a ∈ S ↔
      ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).IsRoot a := by
    intro a
    rw [hS, mem_rootSet, IsRoot.def, eval_map_algebraMap]
    exact ⟨fun h => h.2, fun h => ⟨minpoly.ne_zero hint, h⟩⟩
  set T := {W : Place K F |
    W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring} with hT
  let Φ : T → S := fun W =>
    ⟨αv W.1 (hb W.1) W.2 θ, (hmemS _).mpr (isRoot_alpha (hb W.1) W.2 hπ)⟩
  have hΦinj : Function.Injective Φ := by
    intro W₁ W₂ h
    apply Subtype.ext
    exact eq_of_alpha_eq hgen (hb _) (hb _) W₁.2 W₂.2 hπ hθb hμKsep (congrArg Subtype.val h)
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨a, ha⟩
    obtain ⟨W, hW, hWa⟩ := exists_place_of_isRoot hLD hsepx hb v hπ ((hmemS a).mp ha)
    exact ⟨⟨W, hW⟩, Subtype.ext hWa⟩
  refine ⟨?_, ?_, ?_⟩
  · have : Finite T := Finite.of_injective Φ hΦinj
    exact Set.finite_coe_iff.mp this
  · rw [Nat.card_eq_of_bijective Φ ⟨hΦinj, hΦsurj⟩, Nat.card_eq_fintype_card,
      card_rootSet_eq_natDegree hμsep (IsAlgClosed.splits _), hd]
  · intro W₁ W₂ hW₁ hW₂ H
    have hα : αv W₁ (hb W₁) hW₁ θ = αv W₂ (hb W₂) hW₂ θ := by
      symm
      apply alpha_eq_of_mem_nonunits
      exact H (θ : F₀) θ.2 _ (theta_sub_alpha_mem (hb W₁) hW₁ θ)
    exact eq_of_alpha_eq hgen (hb _) (hb _) hW₁ hW₂ hπ hθb hμKsep hα

end
end S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint
end P2MW
export P2MW.S_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint (solution)
