-- Prove2me | solution 1 for AlgebraicCurve.Place.ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ce80e646-21f1-5717-9901-aae3f387a09c

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint
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
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord_zero Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable Place.mem_iff_ord_nonneg Place.mk_mem_maximalIdeal_iff"
p2m_open "AlgebraicCurve"
namespace CFEFibreGen

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

def resK (W : Place K F) : W.toValuationSubring →ₐ[K] W.ResidueField :=
  { IsLocalRing.residue W.toValuationSubring with commutes' := fun _ => rfl }

@[scoped simp] theorem resK_apply (W : Place K F) (g : W.toValuationSubring) :
    resK W g = IsLocalRing.residue _ g := rfl

theorem mem_nonunits_iff_residue_eq_zero (W : Place K F) (g : W.toValuationSubring) :
    (g : F) ∈ W.toValuationSubring.nonunits ↔ IsLocalRing.residue _ g = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  have h := mk_mem_maximalIdeal_iff_mem_nonunits W.toValuationSubring g.2
  simp only [Subtype.coe_eta] at h
  exact h.symm

theorem coe_aeval_mk (W : Place K F) {x : F} (hx : x ∈ W.toValuationSubring) (P : K[X]) :
    ((aeval (⟨x, hx⟩ : W.toValuationSubring) P : W.toValuationSubring) : F) = aeval x P := by
  have := aeval_algebraMap_apply F (⟨x, hx⟩ : W.toValuationSubring) P
  exact this.symm

theorem aeval_mem (W : Place K F) {x : F} (hx : x ∈ W.toValuationSubring) (P : K[X]) :
    aeval x P ∈ W.toValuationSubring := by
  rw [← coe_aeval_mk W hx P]
  exact Subtype.mem _

theorem residue_aeval_mk (W : Place K F) {x : F} (hx : x ∈ W.toValuationSubring) (P : K[X]) :
    IsLocalRing.residue _ (⟨aeval x P, aeval_mem W hx P⟩ : W.toValuationSubring)
      = aeval (IsLocalRing.residue _ (⟨x, hx⟩ : W.toValuationSubring)) P := by
  have h1 : (⟨aeval x P, aeval_mem W hx P⟩ : W.toValuationSubring)
      = aeval (⟨x, hx⟩ : W.toValuationSubring) P := by
    apply Subtype.ext
    rw [coe_aeval_mk]
  rw [h1, ← resK_apply, ← aeval_algHom_apply, resK_apply]

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

def αW {v : Place k F₀} (W : Place K F) (hW : Over v W) (θ : v.toValuationSubring) :
    W.ResidueField :=
  IsLocalRing.residue _ ⟨ι (θ : F₀), theta_mem hW θ⟩

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

theorem residue_eq_aeval {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) {r r' : F} (hr' : r' ∈ Rv K F v)
    {P : K[X]} (hr : r = aeval (ι (θ : F₀)) P + ι (π : F₀) * r')
    (hrW : r ∈ W.toValuationSubring) :
    IsLocalRing.residue _ (⟨r, hrW⟩ : W.toValuationSubring) = aeval (αW W hW θ) P := by
  have hΘ := theta_mem hW θ
  have hr'W : r' ∈ W.toValuationSubring := Rv_le_of_over hW hr'
  have hPiu := pi_mem_nonunits (K := K) (F := F) hW hπ
  have hPiW : ι (π : F₀) ∈ W.toValuationSubring := nonunits_le _ hPiu
  have hdec : (⟨r, hrW⟩ : W.toValuationSubring)
      = ⟨aeval (ι (θ : F₀)) P, aeval_mem W hΘ P⟩ + ⟨ι (π : F₀), hPiW⟩ * ⟨r', hr'W⟩ := by
    apply Subtype.ext
    simp [hr]
  have hPi0 : IsLocalRing.residue _ (⟨ι (π : F₀), hPiW⟩ : W.toValuationSubring) = 0 :=
    (mem_nonunits_iff_residue_eq_zero W _).mp hPiu
  rw [hdec, map_add, map_mul, hPi0, zero_mul, add_zero, residue_aeval_mk]
  rfl

theorem mem_of_decomp {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) {r r' : F} (hr' : r' ∈ Rv K F v)
    {P : K[X]} (hr : r = aeval (ι (θ : F₀)) P + ι (π : F₀) * r') :
    r ∈ W.toValuationSubring := by
  rw [hr]
  exact add_mem (aeval_mem W (theta_mem hW θ) P)
    (mul_mem (nonunits_le _ (pi_mem_nonunits (K := K) (F := F) hW hπ)) (Rv_le_of_over hW hr'))

theorem mem_nonunits_iff_aeval_eq_zero {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) {r r' : F} (hr' : r' ∈ Rv K F v)
    {P : K[X]} (hr : r = aeval (ι (θ : F₀)) P + ι (π : F₀) * r') :
    r ∈ W.toValuationSubring.nonunits ↔ aeval (αW W hW θ) P = 0 := by
  have hrW : r ∈ W.toValuationSubring := mem_of_decomp hW hπ hr' hr
  rw [show (r ∈ W.toValuationSubring.nonunits)
      = (((⟨r, hrW⟩ : W.toValuationSubring) : F) ∈ W.toValuationSubring.nonunits) from rfl,
    mem_nonunits_iff_residue_eq_zero W, residue_eq_aeval hW hπ hr' hr hrW]

theorem aeval_alpha_minpoly_map {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) :
    aeval (αW W hW θ) ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)) = 0 := by
  obtain ⟨g, hg⟩ := exists_aeval_minpoly_eq v hπ (θ := θ)
  have hPiu := pi_mem_nonunits (K := K) (F := F) hW hπ
  have heq : aeval (ι (θ : F₀)) ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
      = aeval (ι (θ : F₀)) ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K))
        + ι (π : F₀) * 0 := by ring
  rw [← mem_nonunits_iff_aeval_eq_zero hW hπ (zero_mem _) heq, ← algebraMap_coe_aeval, hg]
  push_cast
  rw [mul_comm]
  exact mul_mem_nonunits _ (Rv_le_of_over hW (coe_mem_Rv v g)) hPiu

theorem isIntegral_alpha {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π) :
    IsIntegral K (αW W hW θ) := by
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  refine ⟨(minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K),
    (minpoly.monic hint).map _, ?_⟩
  rw [← aeval_def]
  exact aeval_alpha_minpoly_map hW hπ

def pW {v : Place k F₀} (W : Place K F) (hW : Over v W) (θ : v.toValuationSubring) : K[X] :=
  minpoly K (αW W hW θ)

theorem pW_monic {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π) : (pW W hW θ).Monic :=
  minpoly.monic (isIntegral_alpha hW hπ)

theorem pW_irreducible {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π) :
    Irreducible (pW W hW θ) :=
  minpoly.irreducible (isIntegral_alpha hW hπ)

theorem pW_dvd_iff {v : Place k F₀} {W : Place K F} (hW : Over v W)
    (θ : v.toValuationSubring) (P : K[X]) :
    pW W hW θ ∣ P ↔ aeval (αW W hW θ) P = 0 := by
  constructor
  · rintro ⟨Q, hQ⟩
    rw [hQ, map_mul, pW, minpoly.aeval, zero_mul]
  · intro h
    exact minpoly.dvd K _ h

theorem pW_dvd_minpoly_map {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) :
    pW W hW θ ∣ (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) :=
  (pW_dvd_iff hW θ _).mpr (aeval_alpha_minpoly_map hW hπ)

theorem mem_nonunits_iff_pW_dvd {v : Place k F₀} {W : Place K F} (hW : Over v W)
    {θ π : v.toValuationSubring} (hπ : Irreducible π) {r r' : F} (hr' : r' ∈ Rv K F v)
    {P : K[X]} (hr : r = aeval (ι (θ : F₀)) P + ι (π : F₀) * r') :
    r ∈ W.toValuationSubring.nonunits ↔ pW W hW θ ∣ P := by
  rw [mem_nonunits_iff_aeval_eq_zero hW hπ hr' hr, pW_dvd_iff]

def qW {v : Place k F₀} (W : Place K F) (hW : Over v W) (θ : v.toValuationSubring) : K[X] :=
  ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)) /ₘ pW W hW θ

theorem pW_mul_qW {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π) :
    pW W hW θ * qW W hW θ = (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) := by
  have hmonic := pW_monic (θ := θ) hW hπ
  have h := Polynomial.modByMonic_add_div
    ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)) (pW W hW θ)
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr (pW_dvd_minpoly_map hW hπ),
    zero_add] at h
  exact h

theorem e_notMem_nonunits {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    aeval (ι (θ : F₀)) (qW W hW θ) ∉ W.toValuationSubring.nonunits := by
  have heq : aeval (ι (θ : F₀)) (qW W hW θ)
      = aeval (ι (θ : F₀)) (qW W hW θ) + ι (π : F₀) * 0 := by ring
  rw [mem_nonunits_iff_pW_dvd hW hπ (zero_mem _) heq]
  intro hdvd
  have hsq : pW W hW θ * pW W hW θ ∣
      (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) := by
    rw [← pW_mul_qW hW hπ]
    exact mul_dvd_mul_left _ hdvd
  exact (pW_irreducible hW hπ).not_isUnit (hsep.squarefree _ hsq)

theorem e_mul_eq {v : Place k F₀} [Module.Finite k v.ResidueField] {W : Place K F}
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    {r : F} (hr : r ∈ Rv K F v) (hru : r ∈ W.toValuationSubring.nonunits) :
    ∃ r₂ ∈ Rv K F v, aeval (ι (θ : F₀)) (qW W hW θ) * r = ι (π : F₀) * r₂ := by
  set μK := (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) with hμK
  obtain ⟨P, r', hr', hrP⟩ := exists_decomp v hπ hθ hr
  have hdvd : pW W hW θ ∣ P := (mem_nonunits_iff_pW_dvd hW hπ hr' hrP).mp hru
  obtain ⟨P', hP'⟩ := hdvd
  obtain ⟨g, hg⟩ := exists_aeval_minpoly_eq v hπ (θ := θ)
  have haeμ : aeval (ι (θ : F₀)) μK = ι (π : F₀) * ι (g : F₀) := by
    rw [hμK, ← algebraMap_coe_aeval, hg]; push_cast; ring
  have hΘ : ι (θ : F₀) ∈ Rv K F v := coe_mem_Rv v θ
  refine ⟨ι (g : F₀) * aeval (ι (θ : F₀)) P' + aeval (ι (θ : F₀)) (qW W hW θ) * r', ?_, ?_⟩
  · exact add_mem (mul_mem (coe_mem_Rv v g) (aeval_mem_Rv v hΘ _))
      (mul_mem (aeval_mem_Rv v hΘ _) hr')
  · have key : aeval (ι (θ : F₀)) (qW W hW θ) * aeval (ι (θ : F₀)) P
        = ι (π : F₀) * (ι (g : F₀) * aeval (ι (θ : F₀)) P') := by
      rw [← map_mul, hP', ← mul_assoc, mul_comm (qW W hW θ), pW_mul_qW hW hπ, ← hμK,
        map_mul, haeμ, mul_assoc]
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
    (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable)
    {r : F} (hr : r ∈ Rv K F v) (hr0 : r ≠ 0) :
    ∃ n : ℕ, ∃ s ∈ Rv K F v, ∃ u ∈ Rv K F v, s ∉ W.toValuationSubring.nonunits ∧
      u ∉ W.toValuationSubring.nonunits ∧ s * r = ι (π : F₀) ^ n * u := by
  set e := aeval (ι (θ : F₀)) (qW W hW θ) with he
  have heR : e ∈ Rv K F v := aeval_mem_Rv v (coe_mem_Rv v θ) _
  have heu : e ∉ W.toValuationSubring.nonunits := e_notMem_nonunits hW hπ hsep
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
    · obtain ⟨r₂, hr₂, her⟩ := e_mul_eq hW hπ hθ hr hru
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

theorem div_mem_nonunits_iff_of_factor {L : Type*} [Field L] (B : ValuationSubring L)
    {ϖ r s sr ur ss us : L} (hϖ : ϖ ∈ B.nonunits) (hϖ0 : ϖ ≠ 0)
    (hsrB : sr ∈ B) (hurB : ur ∈ B) (hssB : ss ∈ B) (husB : us ∈ B)
    (hsr : sr ∉ B.nonunits) (hur : ur ∉ B.nonunits) (hss : ss ∉ B.nonunits)
    (hus : us ∉ B.nonunits) (hs0 : s ≠ 0) {a b : ℕ}
    (hfr : sr * r = ϖ ^ a * ur) (hfs : ss * s = ϖ ^ b * us) :
    r / s ∈ B.nonunits ↔ b < a := by
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
  rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀ hvs0, hvr, hvs]
  exact pow_lt_pow_iff_right_of_lt_one₀ hγ0 hγ1

theorem ord_pi_eq_one {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    W.ord (ι (π : F₀)) = 1 := by
  have hPi0 : ι (π : F₀) ≠ 0 := pi_ne_zero hπ
  have hPipos : 0 < W.ord (ι (π : F₀)) :=
    ord_pos_of_mem_nonunits W (pi_mem_nonunits (K := K) (F := F) hW hπ) hPi0

  have hR : ∀ r ∈ Rv K F v, r ≠ 0 → (W.ord (ι (π : F₀))) ∣ W.ord r := by
    intro r hr hr0
    obtain ⟨n, s, hs, u, hu, hsu, huu, hfac⟩ := exists_factor hW hπ hθ hsep hr hr0
    have hs0 : s ≠ 0 := ne_zero_of_notMem_nonunits _ hsu
    have hu0 : u ≠ 0 := ne_zero_of_notMem_nonunits _ huu
    have h := congrArg W.ord hfac
    rw [W.ord_mul hs0 hr0, W.ord_mul (pow_ne_zero _ hPi0) hu0,
      ord_eq_zero_of_notMem_nonunits W (Rv_le_of_over hW hs) hsu,
      ord_eq_zero_of_notMem_nonunits W (Rv_le_of_over hW hu) huu, zero_add, add_zero,
      ← zpow_natCast, W.ord_zpow] at h
    exact ⟨n, by rw [h, mul_comm]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hϖ1 : W.ord (ϖ : F) = 1 := W.ord_coe_irreducible hϖ
  obtain ⟨r, hr, s, hs, hs0, hrs⟩ := exists_div v hgen (ϖ : F)
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_div] at hrs
    have : W.ord (ϖ : F) = 0 := by rw [hrs, Place.ord_zero]
    omega
  have hdvd : W.ord (ι (π : F₀)) ∣ 1 := by
    rw [← hϖ1, hrs, div_eq_mul_inv, W.ord_mul hr0 (inv_ne_zero hs0), W.ord_inv]
    exact dvd_add (hR r hr hr0) (dvd_neg.mpr (hR s hs hs0))
  have := Int.eq_one_of_dvd_one hPipos.le hdvd
  exact this

theorem ord_algebraMap_eq {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) (f : F₀) :
    W.ord (ι f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  have hu0 : ((u : v.toValuationSubring) : F₀) ≠ 0 := by
    intro h0
    have := u.mul_inv
    rw [Subtype.ext_iff] at this
    push_cast at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have huW : ι ((u : v.toValuationSubring) : F₀) ∉ W.toValuationSubring.nonunits := by
    rw [nonunits_iff_of_over hW, coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal]
    exact fun h => h u.isUnit
  have huW' : ι ((u : v.toValuationSubring) : F₀) ∈ W.toValuationSubring :=
    (mem_iff_of_over hW _).mp u.1.2
  have h1 : W.ord (ι f)
      = W.ord (ι (((u : v.toValuationSubring) : F₀) * (π : F₀) ^ (v.ord f))) := by
    rw [← hu]
  rw [h1, map_mul, map_zpow₀, W.ord_mul ((_root_.map_ne_zero _).mpr hu0)
      (zpow_ne_zero _ (pi_ne_zero hπ)), W.ord_zpow, ord_pi_eq_one hgen hW hπ hθ hsep,
    ord_eq_zero_of_notMem_nonunits W huW' huW]
  ring

theorem residue_mem_adjoin_of_mem_Rv {v : Place k F₀} [Module.Finite k v.ResidueField]
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    {n : F} (hn : n ∈ Rv K F v) (hnW : n ∈ W.toValuationSubring) :
    IsLocalRing.residue _ (⟨n, hnW⟩ : W.toValuationSubring)
      ∈ IntermediateField.adjoin K {αW W hW θ} := by
  obtain ⟨P, n', hn', hnP⟩ := exists_decomp v hπ hθ hn
  rw [residue_eq_aeval hW hπ hn' hnP hnW]
  exact IntermediateField.algebra_adjoin_le_adjoin K _ (aeval_mem_adjoin_singleton K _)

theorem adjoin_alpha_eq_top {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    IntermediateField.adjoin K {αW W hW θ} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr, s, hs, hs0, hrs⟩ := exists_div v hgen (x : F)
  have hPi0 : ι (π : F₀) ≠ 0 := pi_ne_zero hπ
  have hPiu := pi_mem_nonunits (K := K) (F := F) hW hπ
  by_cases hr0 : r = 0
  · have hx0 : x = 0 := by
      apply Subtype.ext
      rw [hrs, hr0, zero_div]
      rfl
    rw [hx0, map_zero]
    exact zero_mem _
  obtain ⟨a, sr, hsr, ur, hur, hsr₁, hur₁, hfr⟩ := exists_factor hW hπ hθ hsep hr hr0
  obtain ⟨b, ss, hss, us, hus, hss₁, hus₁, hfs⟩ := exists_factor hW hπ hθ hsep hs hs0
  have hsrW := Rv_le_of_over hW hsr
  have hurW := Rv_le_of_over hW hur
  have hssW := Rv_le_of_over hW hss
  have husW := Rv_le_of_over hW hus
  have hba : b ≤ a := by
    have hxmem : r / s ∈ W.toValuationSubring := hrs ▸ x.2
    exact (div_mem_iff_of_factor W.toValuationSubring hPiu hPi0 hsrW hurW hssW husW
      hsr₁ hur₁ hss₁ hus₁ hs0 hfr hfs).mp hxmem
  rcases lt_or_eq_of_le hba with hlt | heq
  ·
    have hxu : (x : F) ∈ W.toValuationSubring.nonunits := by
      rw [hrs]
      exact (div_mem_nonunits_iff_of_factor W.toValuationSubring hPiu hPi0 hsrW hurW hssW husW
        hsr₁ hur₁ hss₁ hus₁ hs0 hfr hfs).mpr hlt
    rw [(mem_nonunits_iff_residue_eq_zero W x).mp hxu]
    exact zero_mem _
  ·
    subst heq
    have hus0 : us ≠ 0 := ne_zero_of_notMem_nonunits _ hus₁
    have hss0 : ss ≠ 0 := ne_zero_of_notMem_nonunits _ hss₁
    have hkey : (x : F) * (sr * us) = ur * ss := by
      apply mul_right_cancel₀ hs0
      have hc : r / s * s = r := div_mul_cancel₀ r hs0
      rw [hrs]
      calc r / s * (sr * us) * s = (r / s * s) * sr * us := by ring
        _ = (sr * r) * us := by rw [hc]; ring
        _ = ι (π : F₀) ^ b * ur * us := by rw [hfr]
        _ = ur * (ss * s) := by rw [hfs]; ring
        _ = ur * ss * s := by ring
    have hd : IsLocalRing.residue _ (⟨sr * us, mul_mem hsrW husW⟩ : W.toValuationSubring) ≠ 0 := by
      intro h0
      have := (mem_nonunits_iff_residue_eq_zero W ⟨sr * us, mul_mem hsrW husW⟩).mpr h0
      exact mul_notMem_nonunits _ hsrW husW hsr₁ hus₁ this
    have hprod : x * ⟨sr * us, mul_mem hsrW husW⟩
        = (⟨ur * ss, mul_mem hurW hssW⟩ : W.toValuationSubring) := Subtype.ext hkey
    have hres : IsLocalRing.residue _ x
        = IsLocalRing.residue _ (⟨ur * ss, mul_mem hurW hssW⟩ : W.toValuationSubring)
          / IsLocalRing.residue _ (⟨sr * us, mul_mem hsrW husW⟩ : W.toValuationSubring) := by
      rw [eq_div_iff hd, ← map_mul, hprod]
    rw [hres]
    exact div_mem (residue_mem_adjoin_of_mem_Rv hW hπ hθ (mul_mem hur hss) _)
      (residue_mem_adjoin_of_mem_Rv hW hπ hθ (mul_mem hsr hus) _)

theorem finrank_residueField_eq {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    Module.finrank K W.ResidueField = (pW W hW θ).natDegree := by
  have hint := isIntegral_alpha (θ := θ) hW hπ
  rw [← IntermediateField.finrank_top', ← adjoin_alpha_eq_top hgen hW hπ hθ hsep,
    IntermediateField.adjoin.finrank hint]
  rfl

theorem deg_eq_natDegree_pW {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    W.deg = (pW W hW θ).natDegree :=
  finrank_residueField_eq hgen hW hπ hθ hsep

theorem finite_residueField {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W : Place K F} (hW : Over v W) {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable) :
    Module.Finite K W.ResidueField := by
  apply Module.finite_of_finrank_pos
  rw [finrank_residueField_eq hgen hW hπ hθ hsep]
  exact (pW_irreducible hW hπ).natDegree_pos

theorem nonunits_iff_of_pW_eq {v : Place k F₀} [Module.Finite k v.ResidueField]
    {W₁ W₂ : Place K F} (hW₁ : Over v W₁) (hW₂ : Over v W₂)
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hp : pW W₁ hW₁ θ = pW W₂ hW₂ θ) {r : F} (hr : r ∈ Rv K F v) :
    r ∈ W₁.toValuationSubring.nonunits ↔ r ∈ W₂.toValuationSubring.nonunits := by
  obtain ⟨P, r', hr', hrP⟩ := exists_decomp v hπ hθ hr
  rw [mem_nonunits_iff_pW_dvd hW₁ hπ hr' hrP, mem_nonunits_iff_pW_dvd hW₂ hπ hr' hrP, hp]

theorem eq_of_pW_eq {v : Place k F₀} [Module.Finite k v.ResidueField]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    {W₁ W₂ : Place K F} (hW₁ : Over v W₁) (hW₂ : Over v W₂)
    {θ π : v.toValuationSubring} (hπ : Irreducible π)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    (hsep : ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).Separable)
    (hp : pW W₁ hW₁ θ = pW W₂ hW₂ θ) : W₁ = W₂ := by
  have hPi0 : ι (π : F₀) ≠ 0 := pi_ne_zero hπ
  have hPi₁ := pi_mem_nonunits (K := K) (F := F) hW₁ hπ
  have hPi₂ := pi_mem_nonunits (K := K) (F := F) hW₂ hπ
  have tr : ∀ {x : F}, x ∈ Rv K F v → x ∉ W₁.toValuationSubring.nonunits →
      x ∉ W₂.toValuationSubring.nonunits := fun hx h₁ h₂ =>
    h₁ ((nonunits_iff_of_pW_eq hW₁ hW₂ hπ hθ hp hx).mpr h₂)
  apply Place.ext
  ext x
  obtain ⟨r, hr, s, hs, hs0, rfl⟩ := exists_div v hgen x
  by_cases hr0 : r = 0
  · simp [hr0]
  obtain ⟨a, sr, hsr, ur, hur, hsr₁, hur₁, hfr⟩ := exists_factor hW₁ hπ hθ hsep hr hr0
  obtain ⟨b, ss, hss, us, hus, hss₁, hus₁, hfs⟩ := exists_factor hW₁ hπ hθ hsep hs hs0
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

theorem aeval_ne_pi_mul
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (v : Place k F₀) {θ π : v.toValuationSubring} (hπ : Irreducible π) {q : K[X]} (hq0 : q ≠ 0)
    (hqdeg : q.natDegree < (minpoly k (IsLocalRing.residue _ θ)).natDegree)
    {r₀ : F} (hr₀ : r₀ ∈ Rv K F v) :
    aeval (ι (θ : F₀)) q ≠ ι (π : F₀) * r₀ := by
  intro heq
  set d := (minpoly k (IsLocalRing.residue _ θ)).natDegree with hd

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

theorem exists_place_of_factor
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (hsepx : ∃ x : F, FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    (v : Place k F₀) [Module.Finite k v.ResidueField] {θ π : v.toValuationSubring}
    (hπ : Irreducible π) {p : K[X]} (hpm : p.Monic) (hpi : Irreducible p)
    (hpd : p ∣ (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)) :
    ∃ W : Place K F, ∃ hW : Over v W, pW W hW θ = p := by
  classical
  set μK := (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) with hμK
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  have hμK0 : μK ≠ 0 := ((minpoly.monic hint).map _).ne_zero

  set q := μK /ₘ p with hq
  have hpq : p * q = μK := by
    have h := Polynomial.modByMonic_add_div μK p
    rw [(Polynomial.modByMonic_eq_zero_iff_dvd hpm).mpr hpd, zero_add] at h
    exact h
  have hq0 : q ≠ 0 := by
    intro h; rw [h, mul_zero] at hpq; exact hμK0 hpq.symm
  have hqdeg : q.natDegree < (minpoly k (IsLocalRing.residue _ θ)).natDegree := by
    have h1 : q.natDegree = μK.natDegree - p.natDegree := by
      rw [hq]; exact natDegree_divByMonic _ hpm
    have h2 : p.natDegree ≤ μK.natDegree := natDegree_le_of_dvd hpd hμK0
    have h3 : 0 < p.natDegree := hpi.natDegree_pos
    have h4 : μK.natDegree = (minpoly k (IsLocalRing.residue _ θ)).natDegree := by
      rw [hμK, natDegree_map]
    omega
  let A : Subring F := (Rv K F v).toSubring
  have hPiA : ι (π : F₀) ∈ A := coe_mem_Rv v π
  have hΘ : ι (θ : F₀) ∈ Rv K F v := coe_mem_Rv v θ
  have hpA : aeval (ι (θ : F₀)) p ∈ A := aeval_mem_Rv v hΘ p
  let I : Ideal A := Ideal.span {⟨ι (π : F₀), hPiA⟩, ⟨aeval (ι (θ : F₀)) p, hpA⟩}

  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1
    have hab' : (a : F) * ι (π : F₀) + (b : F) * aeval (ι (θ : F₀)) p = 1 := by
      have := congrArg Subtype.val hab
      simpa using this
    obtain ⟨g, hg⟩ := exists_aeval_minpoly_eq v hπ (θ := θ)
    have haeμ : aeval (ι (θ : F₀)) μK = ι (π : F₀) * ι (g : F₀) := by
      rw [hμK, ← algebraMap_coe_aeval, hg]; push_cast; ring
    have hqp : aeval (ι (θ : F₀)) q * aeval (ι (θ : F₀)) p = ι (π : F₀) * ι (g : F₀) := by
      rw [← map_mul, mul_comm q, hpq, haeμ]
    have key : aeval (ι (θ : F₀)) q
        = ι (π : F₀) * (aeval (ι (θ : F₀)) q * a + b * ι (g : F₀)) := by
      calc aeval (ι (θ : F₀)) q
          = aeval (ι (θ : F₀)) q * ((a : F) * ι (π : F₀)
              + (b : F) * aeval (ι (θ : F₀)) p) := by rw [hab', mul_one]
        _ = ι (π : F₀) * (aeval (ι (θ : F₀)) q * a)
              + b * (aeval (ι (θ : F₀)) q * aeval (ι (θ : F₀)) p) := by ring
        _ = ι (π : F₀) * (aeval (ι (θ : F₀)) q * a + b * ι (g : F₀)) := by rw [hqp]; ring
    refine aeval_ne_pi_mul hLD v hπ hq0 hqdeg ?_ key
    exact add_mem (mul_mem (aeval_mem_Rv v hΘ _) a.2) (mul_mem b.2 (coe_mem_Rv v g))

  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hPiB : ι (π : F₀) ∈ B.nonunits :=
    hIB ⟨⟨ι (π : F₀), hPiA⟩, Ideal.subset_span (by simp), rfl⟩
  have hpB : aeval (ι (θ : F₀)) p ∈ B.nonunits :=
    hIB ⟨⟨_, hpA⟩, Ideal.subset_span (by simp), rfl⟩
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
  refine ⟨W, hW, ?_⟩

  have hroot : aeval (αW W hW θ) p = 0 := by
    have heq : aeval (ι (θ : F₀)) p = aeval (ι (θ : F₀)) p + ι (π : F₀) * 0 := by ring
    rw [← mem_nonunits_iff_aeval_eq_zero hW hπ (zero_mem _) heq, hWB']
    exact hpB
  have hdvd : pW W hW θ ∣ p := (pW_dvd_iff hW θ p).mpr hroot
  exact eq_of_monic_of_associated (pW_monic hW hπ) hpm
    ((pW_irreducible hW hπ).associated_of_dvd hpi hdvd)

end Existence

section Counting

open scoped Classical

variable {K : Type*} [Field K]

def monicFactors (μ : K[X]) : Finset K[X] :=
  (UniqueFactorizationMonoid.normalizedFactors μ).toFinset

theorem mem_monicFactors_iff {μ : K[X]} (hμ : μ ≠ 0) (p : K[X]) :
    p ∈ monicFactors μ ↔ p.Monic ∧ Irreducible p ∧ p ∣ μ := by
  classical
  rw [monicFactors, Multiset.mem_toFinset]
  constructor
  · intro hp
    have hirr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    have hnorm : normalize p = p := UniqueFactorizationMonoid.normalize_normalized_factor p hp
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp⟩
    rw [← hnorm]
    exact Polynomial.monic_normalize hirr.ne_zero
  · rintro ⟨hm, hirr, hdvd⟩
    obtain ⟨q, hq, hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hμ hirr hdvd
    have hqirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hqm : q.Monic := by
      rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
      exact Polynomial.monic_normalize hqirr.ne_zero
    rwa [eq_of_monic_of_associated hm hqm hpq]

theorem sum_natDegree_monicFactors {μ : K[X]} (hm : μ.Monic) (hsq : Squarefree μ) :
    ∑ p ∈ monicFactors μ, p.natDegree = μ.natDegree := by
  classical
  have hμ0 : μ ≠ 0 := hm.ne_zero
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors μ).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hμ0).mp hsq
  have hmonic : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors μ, p.Monic := by
    intro p hp
    exact ((mem_monicFactors_iff hμ0 p).mp (Multiset.mem_toFinset.mpr hp)).1
  have hprodm : (UniqueFactorizationMonoid.normalizedFactors μ).prod.Monic := by
    have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors μ) id
      hmonic
    simpa using this
  have hprod : (UniqueFactorizationMonoid.normalizedFactors μ).prod = μ :=
    eq_of_monic_of_associated hprodm hm (UniqueFactorizationMonoid.prod_normalizedFactors hμ0)
  rw [monicFactors, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, hnodup.dedup,
    ← natDegree_multiset_prod_of_monic _ hmonic, hprod]

end Counting

end CFEFibreGen
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint.AlgebraicCurve.CFEFibreGen"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint.AlgebraicCurve.CFEFibreGen P2MW.S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint.AlgebraicCurve AlgebraicCurve.CFEFibreGen Polynomial in
theorem solution
    {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (hsepx : ∃ x : F, FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (v : AlgebraicCurve.Place k F₀) [Module.Finite k v.ResidueField]
    [Algebra.IsSeparable k v.ResidueField] :
    {W : AlgebraicCurve.Place K F |
        W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring}.Finite ∧
    (∀ W : AlgebraicCurve.Place K F,
        W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring →
      (∀ f : F₀, W.ord (algebraMap F₀ F f) = v.ord f) ∧ Module.Finite K W.ResidueField) ∧
    ∀ T : Finset (AlgebraicCurve.Place K F),
      (∀ W, W ∈ T ↔ W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring) →
      ∑ W ∈ T, W.deg = v.deg := by
  classical

  obtain ⟨θb, hθb⟩ := Field.exists_primitive_element k v.ResidueField
  obtain ⟨θ, rfl⟩ := IsLocalRing.residue_surjective θb
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  have hμm : (minpoly k (IsLocalRing.residue _ θ)).Monic := minpoly.monic hint
  have hμsep : (minpoly k (IsLocalRing.residue _ θ)).Separable :=
    Algebra.IsSeparable.isSeparable k _
  set μK := (minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K) with hμK
  have hμKsep : μK.Separable := hμsep.map
  have hμKm : μK.Monic := hμm.map _
  have hμK0 : μK ≠ 0 := hμKm.ne_zero
  have hd : (minpoly k (IsLocalRing.residue _ θ)).natDegree = v.deg :=
    natDegree_minpoly_eq_deg v hθb

  set S := {W : Place K F |
    W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring} with hS
  have hmem : ∀ (W : Place K F) (hW : Over v W), pW W hW θ ∈ monicFactors μK := by
    intro W hW
    rw [mem_monicFactors_iff hμK0]
    exact ⟨pW_monic hW hπ, pW_irreducible hW hπ, pW_dvd_minpoly_map hW hπ⟩
  let Φ : S → monicFactors μK := fun W => ⟨pW W.1 W.2 θ, hmem W.1 W.2⟩
  have hΦinj : Function.Injective Φ := by
    intro W₁ W₂ h
    apply Subtype.ext
    exact eq_of_pW_eq hgen W₁.2 W₂.2 hπ hθb hμKsep (congrArg Subtype.val h)
  refine ⟨?_, ?_, ?_⟩
  · have : Finite S := Finite.of_injective Φ hΦinj
    exact Set.finite_coe_iff.mp this
  · intro W hW
    exact ⟨fun f => ord_algebraMap_eq hgen hW hπ hθb hμKsep f,
      finite_residueField hgen hW hπ hθb hμKsep⟩
  · intro T hT
    have hT' : ∀ W ∈ T, Over v W := fun W hW => (hT W).mp hW
    calc ∑ W ∈ T, W.deg
        = ∑ W ∈ T.attach, (pW W.1 (hT' W.1 W.2) θ).natDegree := by
          rw [← Finset.sum_attach]
          refine Finset.sum_congr rfl fun W _ => ?_
          exact deg_eq_natDegree_pW hgen (hT' W.1 W.2) hπ hθb hμKsep
      _ = ∑ p ∈ monicFactors μK, p.natDegree := by
          apply Finset.sum_bij (fun (W : {W // W ∈ T}) _ => pW W.1 (hT' W.1 W.2) θ)
          · intro W _
            exact hmem W.1 (hT' W.1 W.2)
          · intro W₁ _ W₂ _ h
            apply Subtype.ext
            exact eq_of_pW_eq hgen (hT' W₁.1 W₁.2) (hT' W₂.1 W₂.2) hπ hθb hμKsep h
          · intro p hp
            obtain ⟨hpm, hpi, hpd⟩ := (mem_monicFactors_iff hμK0 p).mp hp
            obtain ⟨W, hW, hWp⟩ := exists_place_of_factor hLD hsepx v hπ hpm hpi hpd
            exact ⟨⟨W, (hT W).mpr hW⟩, Finset.mem_attach _ _, hWp⟩
          · intro W _
            rfl
      _ = μK.natDegree := sum_natDegree_monicFactors hμKm hμKsep.squarefree
      _ = v.deg := by rw [hμK, natDegree_map, hd]

end
end S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_and_sum_deg_eq_deg_of_comap_eq_of_linearDisjoint (solution)
