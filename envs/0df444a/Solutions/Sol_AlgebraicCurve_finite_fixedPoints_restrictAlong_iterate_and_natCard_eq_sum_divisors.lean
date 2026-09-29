-- Prove2me | solution 1 for AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1d565d92-e005-553e-b420-4b1dff192f0e

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_natCard_setOf_comap_eq_eq_deg_of_linearDisjoint
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_deg_eq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.restrictAlong Place.ramificationIndex Place Place.ext Place.deg IsCurveOver IsCurveOver.finrank_kaehler IsCurveOver.finiteResidue Place.natCard_setOf_comap_eq_eq_deg_of_linearDisjoint Place.finite_setOf_deg_eq"
namespace FrobFix
p2m_open "AlgebraicCurve"

section Comap

variable {K F₀ F : Type*} [Field K] [Field F₀] [Field F] [Algebra K F] [Algebra F₀ F]
  (W : Place K F)

theorem map_ne_zero' {f : F₀} (hf : f ≠ 0) : algebraMap F₀ F f ≠ 0 := by simpa using hf

variable {W} in
theorem mem_comap_iff_ord_nonneg {f : F₀} (hf : f ≠ 0) :
    f ∈ W.toValuationSubring.comap (algebraMap F₀ F) ↔ 0 ≤ W.ord (algebraMap F₀ F f) := by
  rw [ValuationSubring.mem_comap]
  exact W.mem_iff_ord_nonneg (map_ne_zero' hf)

variable {W} in
theorem isUnit_mk_comap_iff {f : F₀} (hf : f ≠ 0)
    (hmem : f ∈ W.toValuationSubring.comap (algebraMap F₀ F)) :
    IsUnit (⟨f, hmem⟩ : W.toValuationSubring.comap (algebraMap F₀ F)) ↔
      W.ord (algebraMap F₀ F f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F₀) = 1 := by simpa [Subtype.ext_iff] using hb
    have hbne : (b : F₀) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : W.ord (algebraMap F₀ F f) + W.ord (algebraMap F₀ F (b : F₀)) = 0 := by
      rw [← W.ord_mul (map_ne_zero' hf) (map_ne_zero' hbne), ← map_mul, hb', map_one, W.ord_one]
    have h1 : 0 ≤ W.ord (algebraMap F₀ F f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ W.ord (algebraMap F₀ F (b : F₀)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ W.toValuationSubring.comap (algebraMap F₀ F) :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, W.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

variable (hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f))
include hex

theorem e_pos : 0 < Place.ramificationIndex (F := F₀) W := by
  have hne : {n : ℕ | 0 < n ∧ ∃ f : F₀, f ≠ 0 ∧ W.ord (algebraMap F₀ F f) = n}.Nonempty := by
    obtain ⟨f, hf0, hf⟩ := hex
    exact ⟨(W.ord (algebraMap F₀ F f)).toNat, by omega, f, hf0, by omega⟩
  exact (Nat.sInf_mem hne).1

theorem exists_ord_eq_e :
    ∃ f : F₀, f ≠ 0 ∧ W.ord (algebraMap F₀ F f) = Place.ramificationIndex (F := F₀) W := by
  have hne : {n : ℕ | 0 < n ∧ ∃ f : F₀, f ≠ 0 ∧ W.ord (algebraMap F₀ F f) = n}.Nonempty := by
    obtain ⟨f, hf0, hf⟩ := hex
    exact ⟨(W.ord (algebraMap F₀ F f)).toNat, by omega, f, hf0, by omega⟩
  exact (Nat.sInf_mem hne).2

theorem e_dvd_ord {f : F₀} (hf : f ≠ 0) :
    (Place.ramificationIndex (F := F₀) W : ℤ) ∣ W.ord (algebraMap F₀ F f) := by
  obtain ⟨g, hg0, hge⟩ := exists_ord_eq_e W hex
  set e : ℤ := (Place.ramificationIndex (F := F₀) W : ℤ) with he
  have hepos : 0 < e := by
    have := e_pos W hex
    omega
  set m : ℤ := W.ord (algebraMap F₀ F f) with hm
  set q : ℤ := m / e with hq
  have hgq : algebraMap F₀ F (g ^ (-q)) = (algebraMap F₀ F g) ^ (-q) := map_zpow₀ _ _ _
  have hr : W.ord (algebraMap F₀ F (f * g ^ (-q))) = m - e * q := by
    rw [map_mul, W.ord_mul (map_ne_zero' hf)
      (by rw [hgq]; exact zpow_ne_zero _ (map_ne_zero' hg0)), hgq, W.ord_zpow, hge, ← hm]
    ring
  have hmod := Int.emod_nonneg m (by omega : e ≠ 0)
  have hmod' := Int.emod_lt_of_pos m hepos
  have hbridge : m % e = m - e * q := by
    rw [hq]
    exact Int.emod_def m e
  rcases eq_or_lt_of_le (show (0 : ℤ) ≤ m - e * q by omega) with heq | hlt
  · exact ⟨q, by omega⟩
  · exfalso
    have hfg : f * g ^ (-q) ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hg0)
    have hle := W.ramificationIndex_le_ord (F := F₀) hfg (by omega)
    rw [hr, ← he] at hle
    omega

theorem irreducible_mk_comap {g : F₀} (hg0 : g ≠ 0)
    (hmem : g ∈ W.toValuationSubring.comap (algebraMap F₀ F))
    (hge : W.ord (algebraMap F₀ F g) = Place.ramificationIndex (F := F₀) W) :
    Irreducible (⟨g, hmem⟩ : W.toValuationSubring.comap (algebraMap F₀ F)) := by
  have hepos : 0 < Place.ramificationIndex (F := F₀) W := e_pos W hex
  constructor
  · rw [isUnit_mk_comap_iff hg0 hmem, hge]
    omega
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : g = a * b := by simpa [Subtype.ext_iff] using hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hsum : W.ord (algebraMap F₀ F a) + W.ord (algebraMap F₀ F b)
        = Place.ramificationIndex (F := F₀) W := by
      rw [← W.ord_mul (map_ne_zero' ha0) (map_ne_zero' hb0), ← map_mul, ← hab', hge]
    have ha' : 0 ≤ W.ord (algebraMap F₀ F a) := (mem_comap_iff_ord_nonneg ha0).mp ha
    have hb' : 0 ≤ W.ord (algebraMap F₀ F b) := (mem_comap_iff_ord_nonneg hb0).mp hb
    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_mk_comap_iff ha0 ha).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_mk_comap_iff hb0 hb).mpr hb0'.symm)
    exfalso
    have h1 := W.ramificationIndex_le_ord (F := F₀) ha0 hapos
    have h2 := W.ramificationIndex_le_ord (F := F₀) hb0 hbpos
    omega

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (W.toValuationSubring.comap (algebraMap F₀ F)) := by
  obtain ⟨g, hg0, hge⟩ := exists_ord_eq_e W hex
  have hepos : 0 < Place.ramificationIndex (F := F₀) W := e_pos W hex
  have hgmem : g ∈ W.toValuationSubring.comap (algebraMap F₀ F) :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap W hex hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx
  obtain ⟨c, hc⟩ := e_dvd_ord W hex hf
  have hnonneg : 0 ≤ W.ord (algebraMap F₀ F f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (Place.ramificationIndex (F := F₀) W : ℤ) * c
        ≤ (Place.ramificationIndex (F := F₀) W : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : W.ord (algebraMap F₀ F (f / g ^ n)) = 0 := by
    have hkey : algebraMap F₀ F (f / g ^ n)
        = algebraMap F₀ F f * (algebraMap F₀ F g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F₀ F g) n,
        ← zpow_neg]
    rw [hkey, W.ord_mul (map_ne_zero' hf) (zpow_ne_zero _ (map_ne_zero' hg0)),
      W.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ W.toValuationSubring.comap (algebraMap F₀ F) :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : W.toValuationSubring.comap (algebraMap F₀ F)) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : W.toValuationSubring.comap (algebraMap F₀ F)) : F₀) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

theorem comap_ne_top : W.toValuationSubring.comap (algebraMap F₀ F) ≠ ⊤ := by
  obtain ⟨f, hf0, hf⟩ := hex
  intro htop
  have hmem : f⁻¹ ∈ W.toValuationSubring.comap (algebraMap F₀ F) := htop ▸ trivial
  have := (mem_comap_iff_ord_nonneg (inv_ne_zero hf0)).mp hmem
  rw [map_inv₀, W.ord_inv] at this
  omega

omit hex in

def comapPlace (k : Type*) [Field k] [Algebra k F₀] [Algebra k K] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f)) : Place k F₀ where
  toValuationSubring := W.toValuationSubring.comap (algebraMap F₀ F)
  algebraMap_mem' a := by
    show algebraMap F₀ F (algebraMap k F₀ a) ∈ W.toValuationSubring
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K F]
    exact W.algebraMap_mem' _
  ne_top' := comap_ne_top W hex
  isPrincipalIdealRing' := isPrincipalIdealRing_comap W hex

omit hex in
@[scoped simp] theorem comapPlace_toValuationSubring (k : Type*) [Field k] [Algebra k F₀] [Algebra k K]
    [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
    (hex : ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f)) :
    (comapPlace W k hex).toValuationSubring = W.toValuationSubring.comap (algebraMap F₀ F) :=
  rfl

end Comap

section Nonunits

variable {F₀ F : Type*} [Field F₀] [Field F]

theorem mem_nonunits_iff_of_forall_mem_iff {G : Type*} [FunLike G F₀ F] [RingHomClass G F₀ F]
    (g : G) (A : ValuationSubring F₀) (B : ValuationSubring F) (h : ∀ x, x ∈ A ↔ g x ∈ B)
    (x : F₀) : x ∈ A.nonunits ↔ g x ∈ B.nonunits := by
  have hg : Function.Injective g := fun a b hab =>
    (g : F₀ →+* F).injective (by simpa using hab)
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    map_eq_zero_iff g hg, ← map_inv₀, h]

end Nonunits

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_sub_algebraMap_mem_nonunits [IsAlgClosed K] (W : Place K F)
    [Module.Finite K W.ResidueField] {z : F} (hz : z ∈ W.toValuationSubring) :
    ∃ a : K, z - algebraMap K F a ∈ W.toValuationSubring.nonunits := by
  have : Algebra.IsIntegral K W.ResidueField := Algebra.IsIntegral.of_finite K W.ResidueField
  have hbij : Function.Bijective (algebraMap K W.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue W.toValuationSubring ⟨z, hz⟩)
  refine ⟨a, ?_⟩
  have hres : IsLocalRing.residue W.toValuationSubring
      (⟨z, hz⟩ - algebraMap K W.toValuationSubring a) = 0 := by
    rw [map_sub, ← ha, sub_eq_zero]
    exact (IsScalarTower.algebraMap_apply K W.toValuationSubring W.ResidueField a)
  rw [IsLocalRing.residue_eq_zero_iff] at hres
  have := ValuationSubring.coe_mem_nonunits_iff.mpr hres
  simpa using this

end Values

section FiniteResidue

variable {k F₀ : Type*} [Field k] [Field F₀] [Algebra k F₀]

theorem pow_card_pow_sub_mem_nonunits [Finite k] (v : Place k F₀) [Module.Finite k v.ResidueField]
    {f : F₀} (hf : f ∈ v.toValuationSubring) (m : ℕ) :
    f ^ (Nat.card k ^ (v.deg * m)) - f ∈ v.toValuationSubring.nonunits := by
  haveI : Finite v.ResidueField := Module.finite_of_finite k
  letI : Fintype v.ResidueField := Fintype.ofFinite _
  have hcard : Fintype.card v.ResidueField = Nat.card k ^ v.deg := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := k)]
    rfl
  set x : v.toValuationSubring := ⟨f, hf⟩ with hx
  have hres : IsLocalRing.residue v.toValuationSubring (x ^ (Nat.card k ^ (v.deg * m)) - x) = 0 := by
    rw [map_sub, map_pow, pow_mul, ← hcard, FiniteField.pow_card_pow, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hres
  have := ValuationSubring.coe_mem_nonunits_iff.mpr hres
  simpa using this

theorem deg_dvd_of_forall_pow_sub_mem_nonunits [Finite k] (v : Place k F₀)
    [Module.Finite k v.ResidueField] {r : ℕ}
    (h : ∀ f ∈ v.toValuationSubring, f ^ (Nat.card k ^ r) - f ∈ v.toValuationSubring.nonunits) :
    v.deg ∣ r := by
  classical
  haveI : Finite v.ResidueField := Module.finite_of_finite k
  letI : Fintype v.ResidueField := Fintype.ofFinite _
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Nat.card k := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hcard : Fintype.card v.ResidueField = Nat.card k ^ v.deg := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := k)]
    rfl
  have hdpos : 0 < v.deg := by
    change 0 < Module.finrank k v.ResidueField
    exact Module.finrank_pos

  have hall : ∀ y : v.ResidueField, y ^ (Nat.card k ^ r) = y := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have hx := h x x.2
    rw [← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hx

  set d := v.deg with hd
  set s := r % d with hs
  have hall' : ∀ y : v.ResidueField, y ^ (Nat.card k ^ s) = y := by
    intro y
    have hy := hall y
    have hdecomp : r = d * (r / d) + s := (Nat.div_add_mod r d).symm
    rw [hdecomp, pow_add, pow_mul, pow_mul, ← hcard, FiniteField.pow_card_pow] at hy
    exact hy
  by_contra hnd
  have hs0 : s ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hslt : s < d := Nat.mod_lt r hdpos

  have hsub : (Finset.univ : Finset v.ResidueField).val ⊆
      (Polynomial.X ^ (Nat.card k ^ s) - Polynomial.X : Polynomial v.ResidueField).roots := by
    intro y _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_pow_sub_X_ne_zero _ hs0 hq)]
    have hy := hall' y
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hy, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hs0 hq, Finset.card_univ, hcard] at hle
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hq hslt))

end FiniteResidue

section PowMem

variable {F₀ : Type*} [Field F₀]

theorem pow_mem_iff_mem (A : ValuationSubring F₀) {n : ℕ} (hn : n ≠ 0) (g : F₀) :
    g ^ n ∈ A ↔ g ∈ A := by
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

end PowMem

section Iterate

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral) (W : Place K F)
    (x : F) :
    x ∈ (Place.restrictAlong φ hφi W).toValuationSubring ↔ φ x ∈ W.toValuationSubring :=
  Iff.rfl

theorem mem_iterate_restrictAlong_iff (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral) (n : ℕ)
    (W : Place K F) (x : F) :
    x ∈ ((Place.restrictAlong φ hφi)^[n] W).toValuationSubring ↔
      (φ ^ n) x ∈ W.toValuationSubring := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_restrictAlong_iff, ih, pow_succ, AlgHom.mul_apply]

theorem iterate_restrictAlong_eq_self_iff (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (n : ℕ) (W : Place K F) :
    (Place.restrictAlong φ hφi)^[n] W = W ↔
      ∀ x, (φ ^ n) x ∈ W.toValuationSubring ↔ x ∈ W.toValuationSubring := by
  constructor
  · intro h x
    rw [← mem_iterate_restrictAlong_iff φ hφi n W x, h]
  · intro h
    apply Place.ext
    ext x
    rw [mem_iterate_restrictAlong_iff]
    exact h x

theorem pow_apply_algebraMap {F₀ : Type*} [Field F₀] [Algebra F₀ F] (φ : F →ₐ[K] F) {q : ℕ}
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ q)) (n : ℕ) (x : F₀) :
    (φ ^ n) (algebraMap F₀ F x) = algebraMap F₀ F (x ^ q ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, AlgHom.mul_apply, hφ, ih, ← pow_mul, ← pow_succ']

end Iterate

section Constants

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

theorem exists_constantEmbedding :
    ∃ j : k →+* K, ∀ a : k, algebraMap K F (j a) = algebraMap F₀ F (algebraMap k F₀ a) := by
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hmem : ∀ a : k, algebraMap F₀ F (algebraMap k F₀ a) ∈ (algebraMap K F).range := by
    intro a
    set y := algebraMap F₀ F (algebraMap k F₀ a) with hydef
    have hy : y ^ Fintype.card k = y := by
      rw [hydef, ← map_pow, ← map_pow, FiniteField.pow_card]
    have hint : IsIntegral K y := by
      refine ⟨Polynomial.X ^ Fintype.card k - Polynomial.X, ?_, ?_⟩
      · exact (Polynomial.monic_X_pow _).sub_of_left
          (by rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, hy, sub_self]
    have hdeg : (minpoly K y).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    exact minpoly.mem_range_of_degree_eq_one K y hdeg
  choose j hj using fun a => RingHom.mem_range.mp (hmem a)
  have hinj := (algebraMap K F).injective
  refine ⟨{ toFun := j, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hj⟩
  · apply hinj
    rw [hj, map_one, map_one, map_one]
  · intro a b
    apply hinj
    rw [map_mul, hj, hj, hj, map_mul, map_mul]
  · apply hinj
    rw [hj, map_zero, map_zero, map_zero]
  · intro a b
    apply hinj
    rw [map_add, hj, hj, hj, map_add, map_add]

variable [Algebra k K]

omit [IsAlgClosed K] in

theorem mem_range_algebraMap_of_pow_card_eq {y : K} (hy : y ^ Nat.card k = y) :
    y ∈ Set.range (algebraMap k K) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hy'
  set Z : Finset K := insert y (Finset.univ.image (algebraMap k K)) with hZ
  have hyZ : y ∉ Finset.univ.image (algebraMap k K) := by
    intro h
    apply hy'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, ha⟩
  have hcardZ : Z.card = Nat.card k + 1 := by
    rw [hZ, Finset.card_insert_of_notMem hyZ,
      Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsub : Z.val ⊆ (Polynomial.X ^ Nat.card k - Polynomial.X : Polynomial K).roots := by
    intro z hz
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq)]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
    rcases Finset.mem_insert.mp (Finset.mem_val.mp hz) with rfl | hz''
    · exact hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz''
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, hcardZ] at hle
  omega

variable [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem linearDisjoint (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0 := by
  classical
  intro n f c hf hrel
  letI : Fintype k := Fintype.ofFinite k

  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨m, -, hqm⟩ := FiniteField.card k p
  have hq : Nat.card k = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hqm]
  have hq0 : Nat.card k ≠ 0 := by rw [hq]; exact pow_ne_zero _ hp.out.ne_zero
  haveI : CharP F₀ p := charP_of_injective_algebraMap (algebraMap k F₀).injective p
  haveI : CharP F p := charP_of_injective_ringHom (algebraMap F₀ F).injective p
  haveI : CharP K p := ((algebraMap K F).charP_iff_charP p).mpr inferInstance

  let ρ : K ≃+* K := (iterateFrobeniusEquiv K p m).symm
  have hρ : ∀ x : K, (ρ x) ^ Nat.card k = x := by
    intro x
    rw [hq, ← iterateFrobeniusEquiv_def K p m]
    exact (iterateFrobeniusEquiv K p m).apply_symm_apply x

  have hT : ∀ c : Fin n → K,
      (∑ i, algebraMap K F (ρ (c i)) * algebraMap F₀ F (f i)) ^ Nat.card k
        = φ (∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i)) := by
    intro c
    rw [map_sum, hq, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← map_pow (algebraMap K F), ← map_pow (algebraMap F₀ F), ← hq, hρ, map_mul,
      AlgHom.commutes, hφ]

  suffices key : ∀ (N : ℕ) (c : Fin n → K),
      (Finset.univ.filter fun i => c i ≠ 0).card ≤ N →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0 from
    key _ c le_rfl hrel
  intro N
  induction N with
  | zero =>
    intro c hc _ i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ N ih =>
    intro c hc hrel
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne

    set c' : Fin n → K := fun i => c i / c i₀ with hc'def
    have hc'i₀ : c' i₀ = 1 := by simp [c', hi₀]
    have hc'zero : ∀ i, c i = 0 → c' i = 0 := by
      intro i hi
      simp [c', hi]
    have hrel' : ∑ i, algebraMap K F (c' i) * algebraMap F₀ F (f i) = 0 := by
      have : ∑ i, algebraMap K F (c' i) * algebraMap F₀ F (f i)
          = (algebraMap K F (c i₀))⁻¹ * ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [c']
        rw [div_eq_inv_mul, map_mul, map_inv₀, mul_assoc]
      rw [this, hrel, mul_zero]

    set b : Fin n → K := fun i => ρ (c' i) with hbdef
    have hrelb : ∑ i, algebraMap K F (b i) * algebraMap F₀ F (f i) = 0 := by
      have h := hT c'
      rw [hrel', map_zero] at h
      exact (pow_eq_zero_iff hq0).mp h

    set d : Fin n → K := fun i => b i - c' i with hddef
    have hreld : ∑ i, algebraMap K F (d i) * algebraMap F₀ F (f i) = 0 := by
      simp only [d, map_sub, sub_mul, Finset.sum_sub_distrib, hrelb, hrel', sub_zero]
    have hdsupp : (Finset.univ.filter fun i => d i ≠ 0)
        ⊆ (Finset.univ.filter fun i => c i ≠ 0).erase i₀ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_erase, Finset.mem_filter]
      refine ⟨?_, Finset.mem_univ _, ?_⟩
      · rintro rfl
        apply hi
        simp only [d, b, hc'i₀, map_one, sub_self]
      · intro hci
        apply hi
        simp only [d, b, hc'zero i hci, map_zero, sub_self]
    have hdcard : (Finset.univ.filter fun i => d i ≠ 0).card ≤ N := by
      have h1 := Finset.card_le_card hdsupp
      have h2 : i₀ ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi₀]
      rw [Finset.card_erase_of_mem h2] at h1
      omega
    have hd0 := ih d hdcard hreld

    have hfix : ∀ i, c' i ^ Nat.card k = c' i := by
      intro i
      have hbc : b i = c' i := sub_eq_zero.mp (hd0 i)
      conv_lhs => rw [← hbc]
      exact hρ (c' i)
    choose a ha using fun i => mem_range_algebraMap_of_pow_card_eq (k := k) (hfix i)

    have hrelk : ∑ i, a i • f i = 0 := by
      apply (algebraMap F₀ F).injective
      rw [map_sum, map_zero, ← hrel']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply k F₀ F,
        IsScalarTower.algebraMap_apply k K F, ha]
    have hai₀ : a i₀ = 0 := Fintype.linearIndependent_iff.mp hf a hrelk i₀
    have : c' i₀ = 0 := by rw [← ha i₀, hai₀, map_zero]
    rw [hc'i₀] at this
    exact one_ne_zero this

end Constants

section Nontrivial

variable {K F₀ F : Type*} [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra K F] [Algebra F₀ F] [IsCurveOver K F]

theorem exists_ord_pos_of_fixed (k : Type*) [Field k] [Finite k] [Algebra k F₀] [IsCurveOver k F₀]
    (Φ : F →ₐ[K] F) {Q : ℕ} (hQ : 1 < Q)
    (hΦ : ∀ x : F₀, Φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Q))
    (W : Place K F) (hW : ∀ x, Φ x ∈ W.toValuationSubring ↔ x ∈ W.toValuationSubring) :
    ∃ f : F₀, f ≠ 0 ∧ 0 < W.ord (algebraMap F₀ F f) := by
  classical
  by_contra hcon
  push Not at hcon

  have hall : ∀ f : F₀, algebraMap F₀ F f ∈ W.toValuationSubring := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    have h1 := hcon f hf
    have h2 := hcon f⁻¹ (inv_ne_zero hf)
    rw [map_inv₀, W.ord_inv] at h2
    exact (W.mem_iff_ord_nonneg (map_ne_zero' hf)).mpr (by omega)
  haveI : Module.Finite K W.ResidueField := IsCurveOver.finiteResidue W

  have hres : ∀ (z : F) (hz : z ∈ W.toValuationSubring),
      IsLocalRing.residue W.toValuationSubring ⟨Φ z, (hW z).mpr hz⟩ =
        IsLocalRing.residue W.toValuationSubring ⟨z, hz⟩ := by
    intro z hz
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_nonunits W hz
    have hΦa := (mem_nonunits_iff_of_forall_mem_iff Φ W.toValuationSubring
      W.toValuationSubring (fun x => (hW x).symm) _).mp ha
    rw [map_sub, AlgHom.commutes] at hΦa
    have hdiff : Φ z - z ∈ W.toValuationSubring.nonunits := by
      have := sub_mem hΦa ha
      rwa [sub_sub_sub_cancel_right] at this
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hdiff

  let ι' : F₀ →+* W.toValuationSubring := (algebraMap F₀ F).codRestrict W.toValuationSubring hall
  let ρ : F₀ →+* W.ResidueField := (IsLocalRing.residue W.toValuationSubring).comp ι'
  have hρ : ∀ f : F₀, ρ f ^ Q = ρ f := by
    intro f
    rw [← map_pow]
    show IsLocalRing.residue _ (ι' (f ^ Q)) = IsLocalRing.residue _ (ι' f)
    have h1 : ι' (f ^ Q) = ⟨Φ (algebraMap F₀ F f), (hW _).mpr (hall f)⟩ :=
      Subtype.ext (by simp [ι', hΦ])
    have h2 : ι' f = ⟨algebraMap F₀ F f, hall f⟩ := rfl
    rw [h1, h2, hres _ (hall f)]

  set P : Polynomial W.ResidueField := Polynomial.X ^ Q - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hQ
  let g : F₀ → {y // y ∈ P.roots.toFinset} := fun f => ⟨ρ f, by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp only [hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hρ f, sub_self]⟩
  have hg : Function.Injective g := fun a b h => ρ.injective (congrArg Subtype.val h)
  haveI : Finite F₀ := Finite.of_injective g hg
  haveI : Algebra.IsAlgebraic k F₀ := Algebra.IsAlgebraic.of_finite k F₀
  haveI : Algebra.IsSeparable k F₀ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified k F₀ := Algebra.FormallyUnramified.of_isSeparable k F₀
  have h1 := IsCurveOver.finrank_kaehler (K := k) (F := F₀)
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

end Nontrivial

section Fiber

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

def fiber (v : Place k F₀) : Set (Place K F) :=
  {W : Place K F | W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring}

theorem mem_fiber_iff (v : Place k F₀) (W : Place K F) :
    W ∈ fiber (K := K) (F := F) v ↔
      W.toValuationSubring.comap (algebraMap F₀ F) = v.toValuationSubring :=
  Iff.rfl

end Fiber

end AlgebraicCurve.FrobFix
p2m_reactivate "P2MW.S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors.AlgebraicCurve P2MW.S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors.AlgebraicCurve.FrobFix"
p2m_reactivate "P2MW.S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors.AlgebraicCurve"

open AlgebraicCurve.FrobFix in
theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (r : ℕ) (hr : 0 < r) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[r]).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[r]) =
        ∑ d ∈ Nat.divisors r, d * Nat.card {v : AlgebraicCurve.Place k F₀ | v.deg = d} := by
  classical

  obtain ⟨j, hj⟩ := exists_constantEmbedding (k := k) (K := K) (F₀ := F₀) (F := F)
  letI : Algebra k K := j.toAlgebra
  letI : Algebra k F := ((algebraMap K F).comp j).toAlgebra
  haveI : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k F₀ F := IsScalarTower.of_algebraMap_eq fun a => hj a
  letI : Fintype k := Fintype.ofFinite k
  have hq1 : 1 < Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hQ1 : 1 < Nat.card k ^ r := Nat.one_lt_pow hr.ne' hq1

  set fr := AlgebraicCurve.Place.restrictAlong φ hφi with hfrdef
  have hΦ : ∀ x : F₀, (φ ^ r) (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k ^ r) :=
    pow_apply_algebraMap φ hφ r
  have hfix_iff : ∀ W : AlgebraicCurve.Place K F, W ∈ Function.fixedPoints fr^[r] ↔
      ∀ x, (φ ^ r) x ∈ W.toValuationSubring ↔ x ∈ W.toValuationSubring := fun W => by
    rw [Function.mem_fixedPoints_iff, hfrdef, iterate_restrictAlong_eq_self_iff]

  have hLD := linearDisjoint (k := k) (K := K) (F₀ := F₀) (F := F) φ hφ
  have hchild := fun v : AlgebraicCurve.Place k F₀ =>
    AlgebraicCurve.Place.natCard_setOf_comap_eq_eq_deg_of_linearDisjoint hfg hgen hLD v
  have hfibfin : ∀ v : AlgebraicCurve.Place k F₀, (fiber (K := K) (F := F) v).Finite :=
    fun v => (hchild v).1
  have hfibcard : ∀ v : AlgebraicCurve.Place k F₀, Nat.card (fiber (K := K) (F := F) v) = v.deg :=
    fun v => (hchild v).2.1
  have hfibinj : ∀ (v : AlgebraicCurve.Place k F₀) (W₁ W₂ : AlgebraicCurve.Place K F),
      W₁ ∈ fiber (K := K) (F := F) v → W₂ ∈ fiber (K := K) (F := F) v →
      (∀ f : F₀, f ∈ v.toValuationSubring → ∀ a : K,
        algebraMap F₀ F f - algebraMap K F a ∈ W₁.toValuationSubring.nonunits →
        algebraMap F₀ F f - algebraMap K F a ∈ W₂.toValuationSubring.nonunits) → W₁ = W₂ :=
    fun v => (hchild v).2.2

  have hA : ∀ W ∈ Function.fixedPoints fr^[r],
      ∃ v : AlgebraicCurve.Place k F₀, v.deg ∣ r ∧ W ∈ fiber (K := K) (F := F) v := by
    intro W hWfix
    have hW := (hfix_iff W).mp hWfix
    have hex := exists_ord_pos_of_fixed k (φ ^ r) hQ1 hΦ W hW
    refine ⟨comapPlace W k hex, ?_, rfl⟩
    haveI : Module.Finite k (comapPlace W k hex).ResidueField :=
      AlgebraicCurve.IsCurveOver.finiteResidue _
    haveI : Module.Finite K W.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue W
    apply deg_dvd_of_forall_pow_sub_mem_nonunits (comapPlace W k hex)
    intro g hg
    have hgW : algebraMap F₀ F g ∈ W.toValuationSubring := ValuationSubring.mem_comap.mp hg
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_nonunits W hgW
    have hΦa := (mem_nonunits_iff_of_forall_mem_iff (φ ^ r) W.toValuationSubring
      W.toValuationSubring (fun x => (hW x).symm) _).mp ha
    rw [map_sub, hΦ, AlgHom.commutes] at hΦa
    have hdiff : algebraMap F₀ F (g ^ Nat.card k ^ r) - algebraMap F₀ F g
        ∈ W.toValuationSubring.nonunits := by
      have := sub_mem hΦa ha
      rwa [sub_sub_sub_cancel_right] at this
    rw [mem_nonunits_iff_of_forall_mem_iff (algebraMap F₀ F) (comapPlace W k hex).toValuationSubring
      W.toValuationSubring (fun x => Iff.rfl), map_sub]
    exact hdiff

  have hB : ∀ v : AlgebraicCurve.Place k F₀, v.deg ∣ r →
      ∀ W ∈ fiber (K := K) (F := F) v, W ∈ Function.fixedPoints fr^[r] := by
    intro v hdvd W hWv
    obtain ⟨m, hm⟩ := hdvd
    haveI : Module.Finite k v.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue v
    rw [mem_fiber_iff] at hWv
    rw [Function.mem_fixedPoints_iff]
    have hmemW' : ∀ x, x ∈ (fr^[r] W).toValuationSubring ↔ (φ ^ r) x ∈ W.toValuationSubring :=
      mem_iterate_restrictAlong_iff φ hφi r W

    have hW'v : fr^[r] W ∈ fiber (K := K) (F := F) v := by
      rw [mem_fiber_iff, ← hWv]
      ext g
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, hmemW', hΦ, map_pow]
      exact pow_mem_iff_mem _ (by positivity) _

    symm
    refine hfibinj v W (fr^[r] W) hWv hW'v ?_
    intro g hg a hga
    rw [mem_nonunits_iff_of_forall_mem_iff (φ ^ r) (fr^[r] W).toValuationSubring
      W.toValuationSubring hmemW', map_sub, hΦ, AlgHom.commutes]
    have h1 : algebraMap F₀ F (g ^ Nat.card k ^ r) - algebraMap F₀ F g
        ∈ W.toValuationSubring.nonunits := by
      have h0 := pow_card_pow_sub_mem_nonunits v hg m
      rw [← hm] at h0
      have := (mem_nonunits_iff_of_forall_mem_iff (algebraMap F₀ F) v.toValuationSubring
        W.toValuationSubring (fun x => by rw [← hWv]; rfl) _).mp h0
      rwa [map_sub] at this
    have : algebraMap F₀ F (g ^ Nat.card k ^ r) - algebraMap K F a
        = (algebraMap F₀ F (g ^ Nat.card k ^ r) - algebraMap F₀ F g)
          + (algebraMap F₀ F g - algebraMap K F a) := by ring
    rw [this]
    exact add_mem h1 hga

  haveI : Algebra.EssFiniteType k F₀ := by
    obtain ⟨s, hs⟩ := hfg
    exact IntermediateField.fg_top_iff.mp ⟨s, hs⟩
  set V : Set (AlgebraicCurve.Place k F₀) := {v | v.deg ∣ r} with hVdef
  have hVfin : V.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion (Nat.divisors r).finite_toSet fun d _ =>
      AlgebraicCurve.Place.finite_setOf_deg_eq k F₀ d) ?_
    intro v hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
    exact ⟨v.deg, Nat.mem_divisors.mpr ⟨hv, hr.ne'⟩, rfl⟩

  set T : Finset (AlgebraicCurve.Place K F) :=
    hVfin.toFinset.biUnion fun v => (hfibfin v).toFinset with hTdef
  have hFixT : Function.fixedPoints fr^[r] = ↑T := by
    ext W
    simp only [hTdef, Finset.coe_biUnion, Set.mem_iUnion, Set.Finite.coe_toFinset]
    constructor
    · intro hW
      obtain ⟨v, hv, hWv⟩ := hA W hW
      exact ⟨v, hv, hWv⟩
    · rintro ⟨v, hv, hWv⟩
      exact hB v hv W hWv
  refine ⟨hFixT ▸ T.finite_toSet, ?_⟩
  rw [hFixT, Nat.card_coe_set_eq, Set.ncard_coe_finset, hTdef, Finset.card_biUnion]
  · have hcardfib : ∀ v : AlgebraicCurve.Place k F₀, ((hfibfin v).toFinset).card = v.deg := by
      intro v
      rw [← Nat.card_eq_card_finite_toFinset]
      exact hfibcard v
    simp_rw [hcardfib]
    rw [← Finset.sum_fiberwise_of_maps_to (s := hVfin.toFinset) (t := Nat.divisors r)
      (g := AlgebraicCurve.Place.deg)
      (fun v hv => Nat.mem_divisors.mpr ⟨(Set.Finite.mem_toFinset hVfin).mp hv, hr.ne'⟩)]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2, Finset.sum_const,
      smul_eq_mul, mul_comm]
    congr 1
    rw [Nat.card_eq_card_finite_toFinset (AlgebraicCurve.Place.finite_setOf_deg_eq k F₀ d)]
    congr 1
    ext v
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hVdef]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨h ▸ (Nat.mem_divisors.mp hd).1, h⟩
  · intro v₁ _ v₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro W h1 h2
    rw [Set.Finite.mem_toFinset, mem_fiber_iff] at h1 h2
    exact hne (AlgebraicCurve.Place.ext (h1.symm.trans h2))

end S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
end P2MW
export P2MW.S_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors (solution)
