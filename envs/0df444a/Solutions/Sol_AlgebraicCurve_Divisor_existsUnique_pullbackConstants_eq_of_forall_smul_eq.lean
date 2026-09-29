-- Prove2me | solution 1 for AlgebraicCurve.Divisor.existsUnique_pullbackConstants_eq_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ec3a3e6d-d236-5de5-a2bd-99e07f17ecfe

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsLocalRing AlgebraicCurve

namespace P2mSchmidtDescent2

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

theorem nonunits_le (B : ValuationSubring L) {x : L} (hx : x ∈ B.nonunits) : x ∈ B :=
  ValuationSubring.nonunits_subset hx

theorem mk_mem_maximalIdeal_iff_mem_nonunits (B : ValuationSubring L) {x : L} (hx : x ∈ B) :
    (⟨x, hx⟩ : B) ∈ maximalIdeal B ↔ x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩

theorem mem_nonunits_iff_of_forall_mem_iff {L' : Type*} [Field L'] {E : Type*} [FunLike E L L']
    [RingHomClass E L L'] (g : E) (A : ValuationSubring L) (B : ValuationSubring L')
    (h : ∀ x, x ∈ A ↔ g x ∈ B) (x : L) : x ∈ A.nonunits ↔ g x ∈ B.nonunits := by
  have hg : Function.Injective g := fun a b hab =>
    (g : L →+* L').injective (by simpa using hab)
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    map_eq_zero_iff g hg, ← map_inv₀, h]

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
    (g - algebraMap K W.toValuationSubring a).2).mp (by simp at hmem; exact hmem)
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

theorem resHom_eq_of_sub_mem_nonunits (W : Place K F) (hW : ResBij W)
    (g g' : W.toValuationSubring) (h : (g : F) - g' ∈ W.toValuationSubring.nonunits) :
    resHom W hW g = resHom W hW g' := by
  rw [resHom_eq_iff]
  have h' := resHom_spec W hW g'
  have := add_mem_nonunits _ h h'
  convert this using 1
  ring

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

local notation "ι" => algebraMap F₀ F

def Over (v : Place k F₀) (W : Place K F) : Prop :=
  W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring

theorem mem_iff_of_over {v : Place k F₀} {W : Place K F} (hW : Over v W) (f : F₀) :
    f ∈ v.toValuationSubring ↔ ι f ∈ W.toValuationSubring := by
  rw [← ValuationSubring.mem_comap, show W.toValuationSubring.comap (algebraMap F₀ F)
    = v.toValuationSubring from hW]

theorem nonunits_iff_of_over {v : Place k F₀} {W : Place K F} (hW : Over v W) (f : F₀) :
    ι f ∈ W.toValuationSubring.nonunits ↔ f ∈ v.toValuationSubring.nonunits := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [map_zero]
    exact ⟨fun _ => zero_mem_nonunits _, fun _ => zero_mem_nonunits _⟩
  · rw [mem_nonunits_iff_inv_notMem _ hf,
      mem_nonunits_iff_inv_notMem _ ((map_ne_zero (algebraMap F₀ F)).mpr hf), ← map_inv₀,
      ← mem_iff_of_over hW]

open scoped Pointwise

theorem mem_smul_place_iff (g : SemilinearAut K F) (W : Place K F) (x : F) :
    x ∈ (g • W).toValuationSubring ↔ g⁻¹ • x ∈ W.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem smul_mem_smul_place_iff (g : SemilinearAut K F) (W : Place K F) (x : F) :
    g • x ∈ (g • W).toValuationSubring ↔ x ∈ W.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

theorem smul_mem_nonunits_smul_iff (g : SemilinearAut K F) (W : Place K F) (x : F) :
    g • x ∈ (g • W).toValuationSubring.nonunits ↔ x ∈ W.toValuationSubring.nonunits := by
  symm
  exact mem_nonunits_iff_of_forall_mem_iff (SemilinearAut.toRingAut g) W.toValuationSubring
    (g • W).toValuationSubring (fun y => (smul_mem_smul_place_iff g W y).symm) x

theorem over_smul {v : Place k F₀} {W : Place K F} (hW : Over v W) (g : SemilinearAut K F)
    (hg : ∀ x : F₀, g • ι x = ι x) : Over v (g • W) := by
  unfold Over at hW ⊢
  rw [← hW]
  ext f
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, mem_smul_place_iff]
  have : g⁻¹ • ι f = ι f := by
    conv_lhs => rw [← hg f]
    rw [inv_smul_smul]
  rw [this]

end Over

section Transitive

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

theorem coe_aeval (v : Place k F₀) (θ : v.toValuationSubring) (P : k[X]) :
    ((aeval θ P : v.toValuationSubring) : F₀) = aeval (θ : F₀) P :=
  (aeval_algebraMap_apply F₀ θ P).symm

theorem algebraMap_aeval (θ : F₀) (P : k[X]) :
    ι (aeval θ P) = aeval (ι θ) (P.map (algebraMap k K)) := by
  rw [aeval_map_algebraMap, ← aeval_algebraMap_apply]

theorem resHom_algebraMap_aeval {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    (θ : v.toValuationSubring) (P : k[X]) :
    resHom W hb ⟨ι (aeval (θ : F₀) P), (mem_iff_of_over hW _).mp (by
        rw [← coe_aeval]; exact Subtype.mem _)⟩
      = (P.map (algebraMap k K)).eval (αv W hb hW θ) := by
  have hΘ := theta_mem hW θ
  have h1 : (⟨ι (aeval (θ : F₀) P), (mem_iff_of_over hW _).mp (by
        rw [← coe_aeval]; exact Subtype.mem _)⟩ : W.toValuationSubring)
      = ⟨aeval (ι (θ : F₀)) (P.map (algebraMap k K)), aeval_mem W hΘ _⟩ := by
    apply Subtype.ext
    exact algebraMap_aeval (θ : F₀) P
  rw [h1, resHom_aeval]
  rfl

theorem isRoot_alpha {v : Place k F₀} {W : Place K F} (hb : ResBij W) (hW : Over v W)
    (θ : v.toValuationSubring) :
    ((minpoly k (IsLocalRing.residue _ θ)).map (algebraMap k K)).IsRoot (αv W hb hW θ) := by
  set μ := minpoly k (IsLocalRing.residue _ θ) with hμ
  have hmax : aeval θ μ ∈ maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : IsLocalRing.residue v.toValuationSubring (aeval θ μ)
        = aeval (IsLocalRing.residue v.toValuationSubring θ) μ := by
      let r : v.toValuationSubring →ₐ[k] v.ResidueField :=
        { IsLocalRing.residue v.toValuationSubring with commutes' := fun _ => rfl }
      have := aeval_algHom_apply r θ μ
      exact this.symm
    rw [this, hμ, minpoly.aeval]
  have hv : ((aeval θ μ : v.toValuationSubring) : F₀) ∈ v.toValuationSubring.nonunits :=
    (mk_mem_maximalIdeal_iff_mem_nonunits v.toValuationSubring (aeval θ μ).2).mp
      (by simpa using hmax)
  rw [coe_aeval] at hv
  have hW' := (nonunits_iff_of_over hW _).mpr hv
  have h0 := (mem_nonunits_iff_resHom_eq_zero W hb ⟨ι (aeval (θ : F₀) μ),
    nonunits_le _ hW'⟩).mp hW'
  rw [resHom_algebraMap_aeval hb hW θ μ] at h0
  exact h0

variable [IsAlgClosed K] [IsCurveOver K F]

def α {v : Place k F₀} (θ : v.toValuationSubring) (W : Place K F) (hW : Over v W) : K :=
  αv W (resBij_of_isAlgClosed W) hW θ

theorem alpha_smul {v : Place k F₀} (θ : v.toValuationSubring) {W : Place K F} (hW : Over v W)
    (g : SemilinearAut K F) (hg : ∀ x : F₀, g • ι x = ι x) :
    α θ (g • W) (over_smul hW g hg) = SemilinearAut.baseAut g (α θ W hW) := by
  apply alpha_eq_of_mem_nonunits
  have h := theta_sub_alpha_mem (resBij_of_isAlgClosed W) hW θ
  rw [← smul_mem_nonunits_smul_iff g] at h
  rw [smul_sub, hg, SemilinearAut.smul_algebraMap] at h
  exact h

theorem eq_of_alpha_eq [PerfectField k] [IsCurveOver k F₀]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    {v : Place k F₀} (θ : v.toValuationSubring)
    (hθ : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤)
    {W₁ W₂ : Place K F} (h₁ : Over v W₁) (h₂ : Over v W₂)
    (hα : α θ W₁ h₁ = α θ W₂ h₂) : W₁ = W₂ := by
  haveI : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  refine (AlgebraicCurve.Place.natCard_setOf_comap_eq_eq_deg_of_linearDisjoint
    hfg hgen hLD v).2.2 W₁ W₂ h₁ h₂ ?_
  intro f hf a ha

  set θb := IsLocalRing.residue _ θ with hθb
  have hint : IsIntegral k θb := IsIntegral.of_finite k θb
  have hmem : IsLocalRing.residue _ (⟨f, hf⟩ : v.toValuationSubring)
      ∈ (aeval (R := k) θb).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
      ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]
    trivial
  obtain ⟨P, hP⟩ := hmem
  have hdiff : (⟨f, hf⟩ : v.toValuationSubring) - aeval θ P ∈ maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    have hres : IsLocalRing.residue v.toValuationSubring (aeval θ P) = aeval θb P := by
      let r : v.toValuationSubring →ₐ[k] v.ResidueField :=
        { IsLocalRing.residue v.toValuationSubring with commutes' := fun _ => rfl }
      exact (aeval_algHom_apply r θ P).symm
    rw [hres]
    have hP' : aeval θb P = IsLocalRing.residue _ (⟨f, hf⟩ : v.toValuationSubring) := hP
    rw [hP', sub_self]
  have hv : f - aeval (θ : F₀) P ∈ v.toValuationSubring.nonunits := by
    have := (mk_mem_maximalIdeal_iff_mem_nonunits v.toValuationSubring
      ((⟨f, hf⟩ : v.toValuationSubring) - aeval θ P).2).mp (by simp at hdiff; exact hdiff)
    simpa [coe_aeval] using this

  have key : ∀ (W : Place K F) (hW : Over v W),
      resHom W (resBij_of_isAlgClosed W) ⟨algebraMap F₀ F f, (mem_iff_of_over hW f).mp hf⟩
        = (P.map (algebraMap k K)).eval (α θ W hW) := by
    intro W hW
    have hW' := (nonunits_iff_of_over hW _).mpr hv
    rw [map_sub] at hW'
    have hmemP : algebraMap F₀ F (aeval (θ : F₀) P) ∈ W.toValuationSubring :=
      (mem_iff_of_over hW _).mp (by rw [← coe_aeval]; exact Subtype.mem _)
    rw [resHom_eq_of_sub_mem_nonunits W (resBij_of_isAlgClosed W) _ ⟨_, hmemP⟩ hW']
    exact resHom_algebraMap_aeval (resBij_of_isAlgClosed W) hW θ P
  have ha' : resHom W₁ (resBij_of_isAlgClosed W₁)
      ⟨algebraMap F₀ F f, (mem_iff_of_over h₁ f).mp hf⟩ = a :=
    (resHom_eq_iff _ _ _ _).mpr ha
  rw [key W₁ h₁, hα, ← key W₂ h₂] at ha'
  exact (resHom_eq_iff _ _ _ _).mp ha'

theorem exists_smul_eq_of_over [PerfectField k] [IsCurveOver k F₀]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (G : Subgroup (SemilinearAut K F))
    (hG₀ : ∀ g ∈ G, ∀ x : F₀, g • ι x = ι x)
    (hGK : ∀ a : K, (∀ g ∈ G, SemilinearAut.baseAut g a = a) → a ∈ Set.range (algebraMap k K))
    {v : Place k F₀} {W₁ W₂ : Place K F} (h₁ : Over v W₁) (h₂ : Over v W₂) :
    ∃ g ∈ G, g • W₁ = W₂ := by
  classical
  haveI : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsSeparable k v.ResidueField := Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨θb, hθb⟩ := Field.exists_primitive_element k v.ResidueField
  obtain ⟨θ, hθ⟩ := IsLocalRing.residue_surjective θb
  have hθ' : IntermediateField.adjoin k {IsLocalRing.residue _ θ} = ⊤ := by rw [hθ]; exact hθb
  set μ : k[X] := minpoly k (IsLocalRing.residue _ θ) with hμ
  have hint : IsIntegral k (IsLocalRing.residue _ θ) := IsIntegral.of_finite k _
  have hμirr : Irreducible μ := minpoly.irreducible hint
  have hμmonic : μ.Monic := minpoly.monic hint

  have hfin : {W : Place K F | Over v W}.Finite :=
    (AlgebraicCurve.Place.natCard_setOf_comap_eq_eq_deg_of_linearDisjoint hfg hgen hLD v).1

  set O : Finset (Place K F) := hfin.toFinset.filter (fun W => ∃ g ∈ G, g • W₁ = W) with hO
  have hmemO : ∀ W, W ∈ O ↔ ∃ g ∈ G, g • W₁ = W := by
    intro W
    rw [hO, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · rintro ⟨g, hg, rfl⟩
      exact ⟨over_smul h₁ g (hG₀ g hg), g, hg, rfl⟩
  have hoverO : ∀ W ∈ O, Over v W := by
    intro W hW
    obtain ⟨g, hg, rfl⟩ := (hmemO W).mp hW
    exact over_smul h₁ g (hG₀ g hg)
  have hW₁O : W₁ ∈ O := (hmemO W₁).mpr ⟨1, G.one_mem, one_smul _ _⟩

  let αO : Place K F → K := fun W => if hW : Over v W then α θ W hW else 0
  have hαO : ∀ (W) (hW : Over v W), αO W = α θ W hW := fun W hW => dif_pos hW

  set Q : K[X] := ∏ W ∈ O, (X - C (αO W)) with hQ

  have hQfix : ∀ g ∈ G, Q.map (SemilinearAut.baseAut g : K →+* K) = Q := by
    intro g hg
    rw [hQ, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]

    refine Finset.prod_nbij (fun W => g • W) ?_ ?_ ?_ ?_
    · intro W hW
      obtain ⟨g', hg', rfl⟩ := (hmemO W).mp hW
      exact (hmemO _).mpr ⟨g * g', G.mul_mem hg hg', mul_smul _ _ _⟩
    · intro W₁' _ W₂' _ h
      exact MulAction.injective g h
    · intro W hW
      have hW' : g⁻¹ • W ∈ O := by
        obtain ⟨g', hg', rfl⟩ := (hmemO W).mp (Finset.mem_coe.mp hW)
        exact (hmemO _).mpr ⟨g⁻¹ * g', G.mul_mem (G.inv_mem hg) hg', mul_smul _ _ _⟩
      exact ⟨g⁻¹ • W, Finset.mem_coe.mpr hW', smul_inv_smul g W⟩
    · intro W hW
      have hW' := hoverO W hW
      rw [hαO W hW', hαO (g • W) (over_smul hW' g (hG₀ g hg)), alpha_smul θ hW' g (hG₀ g hg)]

  have hQlifts : Q ∈ Polynomial.lifts (algebraMap k K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply hGK
    intro g hg
    have := congrArg (fun P : K[X] => P.coeff n) (hQfix g hg)
    simp only [Polynomial.coeff_map] at this
    exact this
  obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_lifts Q).mp hQlifts

  have hα₁root : aeval (α θ W₁ h₁) μ = 0 := by
    have := isRoot_alpha (resBij_of_isAlgClosed W₁) h₁ θ
    rw [Polynomial.IsRoot.def, eval_map_algebraMap] at this
    exact this
  have hμmin : μ = minpoly k (α θ W₁ h₁) :=
    minpoly.eq_of_irreducible_of_monic hμirr hα₁root hμmonic
  have hQroot : ∀ (W) (hW : Over v W), Q.IsRoot (α θ W hW) → W ∈ O := by
    intro W hW hroot
    rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hroot
    obtain ⟨W', hW'O, h0⟩ := hroot
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at h0
    rw [hαO W' (hoverO W' hW'O)] at h0
    have : W = W' := eq_of_alpha_eq hfg hgen hLD θ hθ' hW (hoverO W' hW'O) h0
    rw [this]
    exact hW'O
  have hQ₀root : aeval (α θ W₁ h₁) Q₀ = 0 := by
    rw [← eval_map_algebraMap, hQ₀, hQ, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨W₁, hW₁O, by simp [hαO W₁ h₁]⟩
  have hdvd : μ ∣ Q₀ := by
    rw [hμmin]
    exact minpoly.dvd k _ hQ₀root
  have hdvdK : μ.map (algebraMap k K) ∣ Q := by
    rw [← hQ₀]
    exact Polynomial.map_dvd _ hdvd

  have h₂root : Q.IsRoot (α θ W₂ h₂) :=
    (isRoot_alpha (resBij_of_isAlgClosed W₂) h₂ θ).dvd hdvdK
  exact (hmemO W₂).mp (hQroot W₂ h₂ h₂root)

end Transitive

section Hyps

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [Algebra k K] [Algebra k F]
  [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem hconst_of_hLD [IsAlgClosed K]
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0) :
    ∀ y : F₀, IsAlgebraic k y → y ∈ (algebraMap k F₀).range := by
  intro y hy
  by_contra hy'

  have hyF : IsAlgebraic K (algebraMap F₀ F y) := by
    have h1 : IsAlgebraic k (algebraMap F₀ F y) := hy.algebraMap
    exact h1.tower_top (L := K)
  have hint : IsIntegral K (algebraMap F₀ F y) := hyF.isIntegral
  have hdeg : (minpoly K (algebraMap F₀ F y)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one K _ hdeg)

  have hli : LinearIndependent k ![(1 : F₀), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · simp only [ht, zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, ht⟩
    · exfalso
      apply hy'
      refine ⟨-s / t, ?_⟩
      rw [map_div₀, map_neg, div_eq_iff (by simpa using ht), neg_eq_iff_add_eq_zero]
      simpa [Algebra.smul_def, mul_comm] using hst

  have hrel : ∑ i, algebraMap K F (![c, -1] i) * algebraMap F₀ F (![(1 : F₀), y] i) = 0 := by
    simp [Fin.sum_univ_two, hc]
  have := hLD 2 ![(1 : F₀), y] ![c, -1] hli hrel 1
  simp at this

theorem adjoin_range_eq_top [Algebra.IsIntegral F₀ F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤ := by
  set S : Subalgebra F₀ F := Algebra.adjoin F₀ (Set.range (algebraMap K F)) with hS
  haveI : Algebra.IsAlgebraic F₀ S := Algebra.IsAlgebraic.of_injective S.val Subtype.val_injective
  have hSF : IsField S := Subalgebra.isField_of_algebraic S

  let T : IntermediateField K F :=
    { carrier := S
      mul_mem' := fun ha hb => S.mul_mem ha hb
      one_mem' := S.one_mem
      add_mem' := fun ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun a => Algebra.subset_adjoin ⟨a, rfl⟩
      inv_mem' := by
        intro x hx
        rcases eq_or_ne x 0 with rfl | hx0
        · rw [inv_zero]; exact S.zero_mem
        obtain ⟨y, hy⟩ := hSF.mul_inv_cancel (a := ⟨x, hx⟩)
          (fun h => hx0 (congrArg Subtype.val h))
        have hy' : x * (y : F) = 1 := congrArg Subtype.val hy
        rw [inv_eq_of_mul_eq_one_right hy']
        exact y.2 }
  have hle : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact S.algebraMap_mem x
  rw [hgen, top_le_iff] at hle
  rw [eq_top_iff]
  intro x _
  have : x ∈ T := by rw [hle]; exact IntermediateField.mem_top
  exact this

end Hyps

section Descent

variable {k K F₀ F : Type*} [Field k] [PerfectField k] [Field K] [IsAlgClosed K]
  [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
  [Algebra.IsAlgebraic k K] [Algebra.IsIntegral F₀ F]
  [IsCurveOver k F₀] [IsCurveOver K F]

theorem main
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (G : Subgroup (SemilinearAut K F))
    (hG₀ : ∀ g ∈ G, ∀ x : F₀, g • algebraMap F₀ F x = algebraMap F₀ F x)
    (hGK : ∀ a : K, (∀ g ∈ G, SemilinearAut.baseAut g a = a) → a ∈ Set.range (algebraMap k K))
    (D : Divisor K F) (hD : ∀ g ∈ G, g • D = D) :
    ∃! D₀ : Divisor k F₀, Divisor.pullbackConstants K F D₀ = D := by
  classical
  haveI : Algebra.IsSeparable k K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hconst := hconst_of_hLD (k := k) (K := K) (F₀ := F₀) (F := F) hLD
  have hgen' := adjoin_range_eq_top (K := K) (F₀ := F₀) (F := F) hgen

  have he : ∀ W : Place K F, (W.forgetConstants (K := k)).ramificationIndex F₀ = 1 := fun W =>
    AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
      hgen' hconst W

  have hsurj : ∀ v : Place k F₀, ∃ W : Place K F, Place.restrictConstants F₀ (K := k) W = v :=
    fun v => AlgebraicCurve.Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
      hgen' hconst (M := F₀) v
  choose lift hlift using hsurj
  have hover_iff : ∀ (v : Place k F₀) (W : Place K F),
      Place.restrictConstants F₀ (K := k) W = v ↔ Over v W := by
    intro v W
    constructor
    · intro h
      exact congrArg Place.toValuationSubring h
    · intro h
      exact Place.ext h

  have hDconst : ∀ W : Place K F, D W = D (lift (Place.restrictConstants F₀ (K := k) W)) := by
    intro W
    set v := Place.restrictConstants F₀ (K := k) W
    have h₁ : Over v (lift v) := (hover_iff v _).mp (hlift v)
    have h₂ : Over v W := (hover_iff v W).mp rfl
    obtain ⟨g, hg, hgW⟩ := exists_smul_eq_of_over hfg hgen hLD G hG₀ hGK h₁ h₂
    conv_lhs => rw [← hD g hg, ← hgW]
    exact SemilinearAut.divisor_smul_apply_smul g D (lift v)

  let D₀ : Divisor k F₀ := Finsupp.onFinset (D.support.image (Place.restrictConstants F₀ (K := k)))
    (fun v => D (lift v)) (by
      intro v hv
      rw [Finset.mem_image]
      exact ⟨lift v, Finsupp.mem_support_iff.mpr hv, hlift v⟩)
  have hD₀ : ∀ v, D₀ v = D (lift v) := fun v => Finsupp.onFinset_apply
  refine ⟨D₀, ?_, ?_⟩
  · ext W
    rw [Divisor.pullbackConstants_apply, he W, Nat.cast_one, one_mul, hD₀, ← hDconst W]
  · intro E hE
    ext v
    have h := congrArg (fun D' : Divisor K F => D' (lift v)) hE
    rw [Divisor.pullbackConstants_apply, he, Nat.cast_one, one_mul, hlift v] at h
    rw [h, hD₀]

end Descent

end P2mSchmidtDescent2

end

open P2mSchmidtDescent2 in
theorem solution
    {k K F₀ F : Type*} [Field k] [PerfectField k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
    [Algebra.IsAlgebraic k K] [Algebra.IsIntegral F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)
    (G : Subgroup (AlgebraicCurve.SemilinearAut K F))
    (hG₀ : ∀ g ∈ G, ∀ x : F₀, g • algebraMap F₀ F x = algebraMap F₀ F x)
    (hGK : ∀ a : K, (∀ g ∈ G, AlgebraicCurve.SemilinearAut.baseAut g a = a) →
      a ∈ Set.range (algebraMap k K))
    (D : AlgebraicCurve.Divisor K F) (hD : ∀ g ∈ G, g • D = D) :
    ∃! D₀ : AlgebraicCurve.Divisor k F₀,
      AlgebraicCurve.Divisor.pullbackConstants K F D₀ = D :=
  main hfg hgen hLD G hG₀ hGK D hD

end S_AlgebraicCurve_Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_existsUnique_pullbackConstants_eq_of_forall_smul_eq (solution)
